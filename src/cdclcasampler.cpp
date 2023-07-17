#include "cdclcasampler.h"
#include <vector>
#include <string>
#include <unistd.h>
#include <chrono>

#include <iostream>
#include <sstream>
#include <pthread.h>

#include <bits/stdc++.h>
using namespace std;

const int kMaxPbOCCSATSeed = 10000000;

CDCLCASampler::CDCLCASampler(string cnf_file_path, int seed): rnd_file_id_gen_(seed)
{
    cnf_file_path_ = cnf_file_path;
    seed_ = seed;
    rng_.seed(seed_);
    SetDefaultPara();
}

CDCLCASampler::~CDCLCASampler()
{
    delete pbo_solver_;
    for (int i = 1; i < parallel_num; i++)delete(cdcl_sampler_list[i]);
    delete cdcl_sampler;
}

void CDCLCASampler::SetDefaultPara()
{
    // cout << "setDefaultPara" << endl;
    candidate_set_size_ = 100;
    candidate_sample_init_solution_set_.resize(candidate_set_size_);
    candidate_testcase_set_.resize(candidate_set_size_);

    parallel_num = 1;

    part_for_sls = candidate_set_size_ >> 1;

    t_wise_ = 2;
    p_init_tuple_info_ = &CDCLCASampler::Init2TupleInfo;
    p_update_tuple_info_ = &CDCLCASampler::Update2TupleInfo;

    context_aware_method_ = 2;

    flag_use_weighted_sampling_ = true;
    p_init_sample_weight_ = &CDCLCASampler::InitSampleWeightByAppearance;
    p_update_sample_weight_ = &CDCLCASampler::UpdateSampleWeightByAppearance;

    SetPureCDCL();

    p_init_context_aware_flip_priority_ = &CDCLCASampler::InitContextAwareFlipPriority;
    p_update_context_aware_flip_priority_ = &CDCLCASampler::UpdateContextAwareFlipPriorityBySampleWeight;

    flag_use_cnf_reduction_ = true;
    p_reduce_cnf_ = &CDCLCASampler::ReduceCNF;

    no_shuffle_var_ = false;

    int pos = cnf_file_path_.find_last_of('/');
    cnf_instance_name_ = cnf_file_path_.substr(pos + 1);
    size_t suffix_pos = cnf_instance_name_.rfind(".cnf");
    if (suffix_pos != string::npos){
        cnf_instance_name_.replace(suffix_pos, 4, "");
    }

    flag_reduced_cnf_as_temp_ = true;
    reduced_cnf_file_path_ = "/tmp/" + get_random_prefix() + "_reduced.cnf";
    testcase_set_save_path_ = "./" + cnf_instance_name_ + "_testcase_set.txt";

    use_upperlimit = false;

    enable_VSIDS = 0;

    final_strategy = 0;
    p_choose_final = &CDCLCASampler::choose_final_plain;

    p_get_gain = &CDCLCASampler::get_gain;
    sample_cnt_ = 1000000;
}

void CDCLCASampler::SetCandidateSetSize(int candidate_set_size)
{
    candidate_set_size_ = candidate_set_size;
    candidate_sample_init_solution_set_.resize(candidate_set_size_);
    candidate_testcase_set_.resize(candidate_set_size_);
}

void CDCLCASampler::SetParallelNum(int parallel_num_){
    cout << "Parallel num: " << parallel_num << endl;
    parallel_num = parallel_num_;
}

void CDCLCASampler::SetTWise(int t_wise)
{
    t_wise_ = t_wise;
    if (t_wise_ == 2)
    {
        p_init_tuple_info_ = &CDCLCASampler::Init2TupleInfo;
        p_update_tuple_info_ = &CDCLCASampler::Update2TupleInfo;
    }
    else if (t_wise_ == 3)
    {
        cout << "c t_wise must be 2!" << endl;
    }
}

void CDCLCASampler::SetWeightedSamplingMethod(bool use_weighted_sampling)
{
    flag_use_weighted_sampling_ = use_weighted_sampling;
    if (flag_use_weighted_sampling_)
    {
        p_init_sample_weight_ = &CDCLCASampler::InitSampleWeightByAppearance;
        p_update_sample_weight_ = &CDCLCASampler::UpdateSampleWeightByAppearance;
    }
    else
    {
        p_init_sample_weight_ = &CDCLCASampler::InitSampleWeightUniformly;
        p_update_sample_weight_ = &CDCLCASampler::EmptyFunRetVoid;
    }
}

void CDCLCASampler::SetCNFReductionMethod(bool use_cnf_reduction)
{
    flag_use_cnf_reduction_ = use_cnf_reduction;
    if (flag_use_cnf_reduction_)
    {
        p_reduce_cnf_ = &CDCLCASampler::ReduceCNF;
    }
    else
    {
        p_reduce_cnf_ = &CDCLCASampler::EmptyFunRetVoid;
    }
}

void CDCLCASampler::SetFinalStrategy(int strategy)
{
    final_strategy = strategy;
    if (strategy == 0){
        p_choose_final = &CDCLCASampler::choose_final_plain;
    } else if (strategy == 1){
        p_choose_final = &CDCLCASampler::choose_final_random_contiguous_solving_simpl;
    } else if (strategy == 2){
        p_choose_final = &CDCLCASampler::choose_final_random_contiguous_solving_nosimpl;
    } else if (strategy == 3){
        p_choose_final = &CDCLCASampler::choose_final_solution_modifying_shuffle;
    } else if (strategy == 4){
        p_choose_final = &CDCLCASampler::choose_final_solution_modifying_noshuffle;
    }
}

void CDCLCASampler::GenerateInitTestcaseSLS()
{
    bool is_sat = pbo_solver_->solve();
    if (is_sat)
    {
        testcase_set_[0] = pbo_solver_->get_sat_solution();
        num_generated_testcase_ = 1;
    }
    else
    {
        cout << "c PbOCCSAT Failed to Find Initial Sat Solution!" << endl;
    }
}

void CDCLCASampler::GenerateInitTestcaseCDCL()
{
    vector<pair<int, int> > sample_prob = get_prob_in(true);
    cdcl_sampler->set_prob(sample_prob);
    testcase_set_.emplace_back(cdcl_sampler->get_solution());
    num_generated_testcase_ = 1;
}

long long CDCLCASampler::Get2TupleMapIndex(long i, long v_i, long j, long v_j)
{
    long long base = (v_i << 1 | v_j) * num_combination_all_possible_;
    long long pos = (2ll * num_var_ - i - 1) * i / 2 + j - i - 1;
    return base + pos;
}

void CDCLCASampler::Init2TupleInfo()
{
    num_combination_all_possible_ = (long long)num_var_ * (num_var_ - 1) / 2;
    num_tuple_all_possible_ = num_combination_all_possible_ * 4;
    already_t_wise = SimpleBitSet(num_tuple_all_possible_);
    count_each_var_positive_uncovered_.resize(num_var_, (num_var_ - 1) * 2);
    count_each_var_negative_uncovered_.resize(num_var_, (num_var_ - 1) * 2);
    num_tuple_ = 0;
}

void CDCLCASampler::Update2TupleInfo()
{
    int index_testcase = num_generated_testcase_ - 1;
    const vector<int>& testcase = testcase_set_[index_testcase];

    for (int i = 0; i < num_var_ - 1; i++)
    {
        for (int j = i + 1; j < num_var_; j++)
        {
            long long index_tuple = Get2TupleMapIndex(i, testcase[i], j, testcase[j]);
            bool res = already_t_wise.set(index_tuple);
            if (res)
            {
                num_tuple_++;
                // if(num_tuple_ == 1000000000)
                    // cout << num_tuple_ << endl;
                if (testcase[i] == 1)
                {
                    count_each_var_positive_uncovered_[i]--;
                }
                else
                {
                    count_each_var_negative_uncovered_[i]--;
                }
                if (testcase[j] == 1)
                {
                    count_each_var_positive_uncovered_[j]--;
                }
                else
                {
                    count_each_var_negative_uncovered_[j]--;
                }
            }
        }
    }

    // cout<<"update tuple info : " << num_tuple_ << endl;
}

void CDCLCASampler::InitSampleWeightByAppearance()
{
    var_positive_appearance_count_.resize(num_var_);
    var_positive_sample_weight_.resize(num_var_);
}

void CDCLCASampler::UpdateSampleWeightByAppearance()
{
    int new_testcase_index = num_generated_testcase_ - 1;
    const vector<int>& new_testcase = testcase_set_[new_testcase_index];
    for (int v = 0; v < num_var_; v++)
    {
        var_positive_appearance_count_[v] += new_testcase[v];
        var_positive_sample_weight_[v] = 1. - double(var_positive_appearance_count_[v]) / num_generated_testcase_;
    }
}

void CDCLCASampler::InitSampleWeightUniformly()
{
    var_positive_sample_weight_.resize(num_var_, 0.5);
}

void CDCLCASampler::InitContextAwareFlipPriority()
{
    context_aware_flip_priority_.resize(num_var_, 0.);
}

void CDCLCASampler::UpdateContextAwareFlipPriority()
{
    vector<int> init_solution = candidate_sample_init_solution_set_[selected_candidate_index_];
    vector<int> sat_testcase = candidate_testcase_set_[selected_candidate_index_];
    vector<int> var_flip_count(num_var_);
    for (int v = 0; v < num_var_; v++)
    {
        var_flip_count[v] = abs(init_solution[v] - sat_testcase[v]);
    }
    for (int v = 0; v < num_var_; v++)
    {
        context_aware_flip_priority_[v] += var_flip_count[v];
    }
    pbo_solver_->set_var_flip_priority_ass_unaware(context_aware_flip_priority_);
}

void CDCLCASampler::UpdateContextAwareFlipPriorityBySampleWeight(const vector<int> &init_solution)
{
    for (int v = 0; v < num_var_; v++)
    {
        if (init_solution[v])
            context_aware_flip_priority_[v] = var_positive_sample_weight_[v];
        else
            context_aware_flip_priority_[v] = 1. - var_positive_sample_weight_[v];
    }

    pbo_solver_->set_var_flip_priority_ass_aware(context_aware_flip_priority_);
}

void CDCLCASampler::ReduceCNF()
{
    string cmd = "./bin/coprocessor -enabled_cp3 -up -subsimp -no-bve -no-bce"
                 " -no-dense -dimacs=" +
                 reduced_cnf_file_path_ + " " + cnf_file_path_;

    int return_val = system(cmd.c_str());

    cnf_file_path_ = reduced_cnf_file_path_;
}

void CDCLCASampler::InitPbOCCSATSolver()
{
    pbo_solver_ = new PbOCCSATSolver(cnf_file_path_, rng_.next(kMaxPbOCCSATSeed), num_var_);
}

void CDCLCASampler::Init()
{
    num_var_ = 0;

    if (!check_no_clauses()){
        (this->*p_reduce_cnf_)();
    } else {
        flag_use_cnf_reduction_ = false;
    }
    
    InitPbOCCSATSolver();

    read_cnf();

    cdcl_sampler = new ExtMinisat::SamplingSolver(num_var_, clauses, seed_, !no_shuffle_var_, enable_VSIDS);
    
    cdcl_sampler_list.emplace_back(cdcl_sampler);
    for (int i = 1; i < parallel_num; i++){
        cdcl_sampler_list.emplace_back(new ExtMinisat::SamplingSolver(num_var_, clauses, seed_*i, !no_shuffle_var_, enable_VSIDS));
    }

    if (flag_use_pure_cdcl_){
        GenerateInitTestcaseCDCL();
    } else {
        GenerateInitTestcaseSLS();
    }
    (this->*p_init_tuple_info_)();
    (this->*p_init_sample_weight_)();
    (this->*p_init_context_aware_flip_priority_)();
}

vector<int> CDCLCASampler::GetSatTestcaseWithGivenInitSolution(const vector<int> &init_solution)
{
    int pbo_seed = rng_.next(kMaxPbOCCSATSeed);
    pbo_solver_->set_seed(pbo_seed);

    pbo_solver_->set_init_solution(init_solution);

    (this->*p_update_context_aware_flip_priority_)(init_solution);

    bool is_sat = pbo_solver_->solve();

    if (is_sat)
    {
        return pbo_solver_->get_sat_solution();
    }
    else
    {
        cout << "c PbOCCSAT Failed to Find Sat Solution!" << endl;
    }
}

vector<int> CDCLCASampler::GetWeightedSampleInitSolution()
{
    vector<int> weighted_sample_init_solution(num_var_, 0);
    for (int v = 0; v < num_var_; v++)
    {
        if (rng_.nextClosed() < var_positive_sample_weight_[v])
        {
            weighted_sample_init_solution[v] = 1;
        }
    }
    return weighted_sample_init_solution;
}

void CDCLCASampler::GenerateCandidateTestcaseSet()
{
    vector<pair<int, int> > sample_prob = get_prob_in(false);

    for (int i = 0; i < part_for_sls; i++){
        candidate_sample_init_solution_set_[i] = GetWeightedSampleInitSolution();
        candidate_testcase_set_[i] = GetSatTestcaseWithGivenInitSolution(candidate_sample_init_solution_set_[i]);
    }
    
    for (int i = part_for_sls; i < candidate_set_size_; i++){
        cdcl_sampler->set_prob(sample_prob);
        cdcl_sampler->get_solution(candidate_testcase_set_[i]);
    }
}

int CDCLCASampler::SelectTestcaseFromCandidateSetByTupleNum()
{
    for (int i = 0; i < candidate_set_size_; ++i){
        pq.emplace_back(candidate_testcase_set_[i], (this->*p_get_gain)(candidate_testcase_set_[i]));
        pq_idx.push_back(0);
    }
    
    iota(pq_idx.begin(), pq_idx.end(), 0);
    sort(pq_idx.begin(), pq_idx.end(), [&](int i, int j){
        return pq[i].second.count() > pq[j].second.count();
    });

    return pq_idx[0];
}

void CDCLCASampler::GenerateTestcase()
{
    GenerateCandidateTestcaseSet();
    selected_candidate_index_ = SelectTestcaseFromCandidateSetByTupleNum();

    int testcase_index = num_generated_testcase_;
    testcase_set_.emplace_back(pq[selected_candidate_index_].first);
    selected_candidate_bitset_ = pq[selected_candidate_index_].second;
}

void CDCLCASampler::GenerateCoveringArray()
{
    auto start_time = chrono::system_clock::now().time_since_epoch();
    Init();

    // cout << "Init." << endl;
    
    (this->*p_update_tuple_info_)();

    cout << "update tuple 1." << endl;
    //
    if(num_tuple_all_possible_ > 1000000){
        cout << "Possible tuples: " << num_tuple_all_possible_ << endl;
        stage_change(2);
        cout << "stage change over." << endl;
    }
    //

    for (num_generated_testcase_ = 1; ; num_generated_testcase_++)
    {
        if (num_generated_testcase_ > 1){
            (this->*p_update_tuple_info_)();
        }
        if (use_upperlimit && upperlimit == num_tuple_){
            break;
        }
        if (num_generated_testcase_ > 1) {
            clear_pq();
        }
        cout << num_generated_testcase_ << ": " << num_tuple_ << endl;
        (this->*p_update_sample_weight_)();
        GenerateTestcase();
        if (!selected_candidate_bitset_.count()){
            testcase_set_.pop_back();
            break;
        }
    }

    //
    p_update_tuple_info_ = &CDCLCASampler::Update2TupleInfo;
    //

    cout << "p: " << parallel_num << endl;

    invalid_tuple_num = 0;

    clear_final();

    cout << "p: " << parallel_num << endl;

    auto end_time = chrono::system_clock::now().time_since_epoch();
    cpu_time_ = chrono::duration_cast<chrono::milliseconds>(end_time - start_time).count() / 1000.0;
    cout << "c Generate testcase set finished, containing " << testcase_set_.size() << " testcases!" << endl;
    cout << "c CPU time cost by generating testcase set: " << cpu_time_ << " seconds" << endl;
    SaveTestcaseSet(testcase_set_save_path_);

    cout << "c " << t_wise_ << "-tuple number of generated testcase set: " << num_tuple_ << endl;

    remove_temp_files();
}

void CDCLCASampler::SaveTestcaseSet(string result_path)
{
    ofstream res_file(result_path);
    for (const vector<int>& testcase: testcase_set_)
    {
        for (int v = 0; v < num_var_; v++)
        {
            res_file << testcase[v] << " ";
        }
        res_file << endl;
    }
    res_file.close();
    cout << "c Testcase set saved in " << result_path << endl;
}

void CDCLCASampler::Update2TupleInfo2(){
    // 不仅会用新加入的 tuple 的信息更新 bitset，还会依照性地对 probnew 进行更新
    const vector<int>& testcase = testcase_set_.back();

    long long tuple_pos = 0;
    for (int i = 0; i < num_var_; ++i){
        long long tuple_id_base0 = testcase[i] ? num_combination_all_possible_ << 1: 0;
        for (int j = i + 1; j < num_var_; ++j, ++tuple_pos){
            long long tuple_id_base1 = testcase[j] ? num_combination_all_possible_: 0;
            long long tuple_id = tuple_id_base0 + tuple_id_base1 + tuple_pos;
            bool res = already_t_wise.set(tuple_id);
            if (res){
                ++num_tuple_;
                if (testcase[i] == 1){
                    --probnew[i].second;
                } else {
                    --probnew[i].first;
                }
                if (testcase[j] == 1){
                    --probnew[j].second;
                } else {
                    --probnew[j].first;
                }
            }
        }
    }
}

struct para3 {
    std::vector<std::vector<int>> *candidate_testcase_set_;
    vector<pair<vector<int>, long long> > *pq;
    vector<int> *pq_idx;
    CDCLCASampler *th;
    int start,end;
    vector<long long> *ret;
};

void *CDCLCASampler::pthread_func4(void *arg){
    struct para3 *p = (struct para3*)arg;
    int i = p->start;
    int j = p->end;
    std::vector<std::vector<int>> *candidate_testcase_set_ = p->candidate_testcase_set_;
    vector<pair<vector<int>, long long> > *pq = p->pq;
    vector<int> *pq_idx = p->pq_idx;
    CDCLCASampler *th=p->th;
    vector<long long> *ret1 = p->ret;
    for(; i<j; i++){
        long long res = th->get_gain5(candidate_testcase_set_->at(i));
        ret1->at(i-p->start)=res;
    }
    free(p);
    pthread_exit(NULL);
}

int CDCLCASampler::SelectTestcaseFromCandidateSetByTupleNum2(){
    int div = candidate_set_size_ / parallel_num;
    pthread_t tid[parallel_num] = {0};
    vector< vector<long long> > ret_table(parallel_num, vector<long long>(div+parallel_num,0));

    for (int i = 0; i < parallel_num; i++){
        int *p = (int*)malloc(sizeof(*p));
        *p = i;
        struct para3 *myp = (struct para3*)malloc(sizeof(struct para3));
        myp->candidate_testcase_set_ = &candidate_testcase_set_;
        myp->pq = &pq_score;
        myp->pq_idx = &pq_idx;
        myp->start = part_for_sls + *p * div;
        myp->th = this;
        myp->ret = &(ret_table[i]);
        if( *p == parallel_num - 1 )myp->end = candidate_set_size_;
        else myp->end = part_for_sls + (*p + 1) * div;
        pthread_create(&tid[*p],NULL,pthread_func4,(void*)myp);
        free(p);
    }
    for (int i = 0; i < parallel_num; i++){
        pthread_join(tid[i],NULL);
        int start = part_for_sls + i*div;
        int k = start;
        int l;
        if( i == parallel_num - 1 )
            l = candidate_set_size_;
        else 
            l = part_for_sls  + ( i + 1 ) * div;
        for(; k<l; k++){
            pq_score.emplace_back(candidate_testcase_set_.at(k), ret_table.at(i).at(k-start));
            pq_idx.push_back(0);
        }
    }

    
    // sort the cache by the scores in descending order
    iota(pq_idx.begin(), pq_idx.end(), 0);
    sort(pq_idx.begin(), pq_idx.end(), [&](int i, int j){
        // 先考虑分数，再考虑 gain
        return pq_score[i].second > pq_score[j].second;
    });
    // choose the highest
    return pq_idx[0];
}

struct para {
    ExtMinisat::SamplingSolver *cdcl_sampler;
    vector<pair<int, int> > *sample_prob;
    std::vector<std::vector<int>> *candidate_testcase_set_;
    int start,end;
};

void *CDCLCASampler::pthread_func3(void *arg){
    struct para *p = (struct para*)arg;
    int i = p->start;
    int j = p->end;
    for(; i<j; i++){
        p->cdcl_sampler->set_prob_backward(*(p->sample_prob));
        p->cdcl_sampler->get_solution(p->candidate_testcase_set_->at(i));
    }
    free(p);
    pthread_exit(NULL);
}

void CDCLCASampler::GenerateCoveringArray2(){
    GenerateCoveringArray();

    auto start_time = chrono::system_clock::now().time_since_epoch();

    unc_num = uncovered_tuples.size();
    cout << "Uncovered tuples: " << unc_num << endl;
    long long res_num;

    // now it begins
    cout << "c second phase ..." << endl;
    as_cnt[0] = vector<int>(num_var_, 0);
    as_cnt[1] = vector<int>(num_var_, 0);

    for (int i = 0; i < unc_num; ++i){
        int j,k,vj,vk;
        j = abs(uncovered_tuples[i][0]) - 1;
        vj = uncovered_tuples[i][0] < 0 ? 0: 1;
        k = abs(uncovered_tuples[i][1]) - 1;
        vk = uncovered_tuples[i][1] < 0 ? 0: 1;
        ++as_cnt[vj][j];
        ++as_cnt[vk][k];
        unc.emplace_back(vj==0?j:-j,vk==0?k:-k);
    }
    
    long long old_num = num_tuple_;

    pq.clear();
    pq_idx.clear();

    probnew.reserve(num_var_);
    for (int i = 0; i < num_var_; ++i)
        probnew.emplace_back(as_cnt[0][i], as_cnt[1][i]);

    int first,second,fsign,ssign;
    vector<int> tmp_testcase;

    part_for_sls = 0;

    cout << "p:" << parallel_num << endl;

    for (; num_tuple_ < num_tuple_all_exact_; ++num_generated_testcase_){
        vector<pair<int, int> > sample_prob2 = get_prob_in2();
        
        int div = (candidate_set_size_ - part_for_sls) / parallel_num;
        pthread_t tid[parallel_num] = {0};
        for (int i = 0; i < parallel_num; i++){
            int *p = (int*)malloc(sizeof(*p));
            *p = i;
            struct para *myp = (struct para*)malloc(sizeof(struct para));
            myp->cdcl_sampler = cdcl_sampler_list[*p];
            myp->sample_prob = &sample_prob2;
            myp->candidate_testcase_set_ = &candidate_testcase_set_;
            myp->start = part_for_sls + *p * div;
            if( *p == parallel_num - 1 )myp->end = candidate_set_size_;
            else myp->end = part_for_sls + (*p + 1) * div;
            pthread_create(&tid[*p],NULL,pthread_func3,(void*)myp);
            free(p);
        }
        for (int i = 0; i < parallel_num; i++)pthread_join(tid[i],NULL);


        selected_candidate_index_ = SelectTestcaseFromCandidateSetByTupleNum2();

        tmp_testcase = pq_score[selected_candidate_index_].first;
        long long i=0;
        unc_tmp.clear();
        while(i < unc_num){
            first = unc[i].first;
            second = unc[i].second;
            fsign = first>0?0:1;
            ssign = second>0?0:1;
            if (tmp_testcase[abs(first)]==fsign && tmp_testcase[abs(second)]==ssign){
                unc_tmp.emplace_back(unc[i]);
                unc[i] = unc[unc_num-1];
                unc_num--;
                i--;
            }
            i++;
        }

        testcase_set_.emplace_back(pq_score[selected_candidate_index_].first);
        res_num = pq_score[selected_candidate_index_].second;
        Update2TupleInfo2();


        clear_pq4(candidate_set_size_);

        if (!res_num){
            testcase_set_.pop_back();
            break;
        }

        cout << num_generated_testcase_ + 1 << ": " << num_tuple_ << endl;
    }
    
    invalid_tuple_num = 0;

    clear_final2();
    // clear_final();

    auto end_time = chrono::system_clock::now().time_since_epoch();
    cpu_time_ = chrono::duration_cast<chrono::milliseconds>(end_time - start_time).count() / 1000.0;
    cout << "c Generate testcase set finished, containing " << testcase_set_.size() << " testcases!" << endl;
    cout << "c CPU time cost by generating testcase set: " << cpu_time_ << " seconds" << endl;
    SaveTestcaseSet(testcase_set_save_path_);
}

void CDCLCASampler::ReadTestcaseSet(string result_path)
{
    ifstream res_file(result_path);
    string line;
    num_generated_testcase_ = 0;
    testcase_set_.clear();
	while (getline(res_file, line)){
		stringstream ss(line);
		string tmp;
		vector<int> v;
		while (getline(ss, tmp, ' ')){
			v.push_back(stoi(tmp));
		}
		testcase_set_.push_back(v);
        num_generated_testcase_ ++ ;
	}
    res_file.close();
    cout<< "c Read Testcase set " << result_path << endl;
}

vector<pair<int, int> > CDCLCASampler::get_prob_in(bool init){
    vector<pair<int, int> > res;
    res.reserve(num_var_);
    if (!init && context_aware_method_ != 0){
        for (int i = 0; i < num_var_; ++i){
            int v1 = context_aware_method_ == 1 ? 0: (num_generated_testcase_ - var_positive_appearance_count_[i]);
            int v2 = context_aware_method_ == 1 ? 0: var_positive_appearance_count_[i];
            res.emplace_back(v1, v2);
        }
    }
    return res;
}

vector<pair<int, int> > CDCLCASampler::get_prob_in2(){
    // 获取每个变量参与的 uncovered 2-tuple 的统计信息
    vector<pair<int, int> > res;
    res.reserve(num_var_);
    for (int i = 0; i < num_var_; ++i){
        int v1 = context_aware_method_ == 1 ? 0: probnew[i].first;
        int v2 = context_aware_method_ == 1 ? 0: probnew[i].second;
        res.emplace_back(v1, v2);
    }
    return res;
}

SimpleBitSet CDCLCASampler::get_gain(const vector<int>& asgn)
{
    SimpleBitSet res(num_tuple_all_possible_);
    for (int i = 0; i < num_var_ - 1; i++)
    {
        for (int j = i + 1; j < num_var_; j++)
        {
            long long index_tuple = Get2TupleMapIndex(i, asgn[i], j, asgn[j]);
            if (!already_t_wise.get(index_tuple)){
                res.set(index_tuple);
            }
        }
    }
    return res;
}

long long CDCLCASampler::get_gain5(const vector<int>& asgn){
    long long res = 0;
    
    for (long long i = 0; i < unc_num; i++){
        int first = unc[i].first,second = unc[i].second;
        int fsign = first>0?0:1,ssign = second>0?0:1;
        if (asgn[abs(first)]==fsign && asgn[abs(second)]==ssign){
            res++;
        }
    }
    
    return res;
}

void CDCLCASampler::remove_temp_files(){
    string cmd;
    int ret;
    if (flag_reduced_cnf_as_temp_ && flag_use_cnf_reduction_){
        cmd = "rm " + reduced_cnf_file_path_;
        ret = system(cmd.c_str());
    }
}

string CDCLCASampler::get_random_prefix()
{
    return cnf_instance_name_ + to_string(getpid()) + to_string(rnd_file_id_gen_());
}

void CDCLCASampler::clear_pq()
{
    for (auto& bs: pq){
        bs.second.difference_(selected_candidate_bitset_);
    }

    sort(pq.begin(), pq.end(), [](const pair<vector<int>, SimpleBitSet>& si, const pair<vector<int>, SimpleBitSet>& sj){
        return si.second.count() > sj.second.count();
    });

    int cur_pqsize = (int) pq.size();
    while (cur_pqsize > candidate_set_size_ || (cur_pqsize > 0 && pq.back().second.count() == 0)){
        pq.pop_back();
        pq_idx.pop_back();
        --cur_pqsize;
    }
}

void CDCLCASampler::clear_pq4(int k_for_this){
    // update the cache with the selected testcase
    int cur_unctmp_size = (int) unc_tmp.size();
    for (auto& bs: pq_score){
        for (long long i = 0; i < cur_unctmp_size; i++){
            int first = unc_tmp[i].first,second = unc_tmp[i].second;
            int fsign = first>0?0:1,ssign = second>0?0:1;
            if (bs.first[abs(first)]==fsign && bs.first[abs(second)]==ssign){
                bs.second--;
            }
        }
    }

    sort(pq_score.begin(), pq_score.end(), [](const pair<vector<int>, long long>& si, const pair<vector<int>, long long>& sj){
        return si.second > sj.second;
    });

    // remove not-so-good or useless testcases in the cache
    // 这么做恰好能删掉本次选中的 testcase
    int cur_pqsize = (int) pq_score.size();
    while (cur_pqsize > k_for_this || (cur_pqsize > 0 && pq_score.back().second == 0)){
        pq_score.pop_back();
        pq_idx.pop_back();
        --cur_pqsize;
    }
}

struct para2{
    CDCLSolver::Solver *cdcl_solver2;
    CDCLCASampler *th;
    long long *num_tuple_all_exact_;
    long long *invalid_tuple_num;
    vector<vector<int> > *uncovered_possible_solutions;
    vector<vector<int> > *uncovered_tuples;
    vector<int> *as_backbone;
    int idx,num_var_,parallel_num;
    bool simplify;
    SimpleBitSet *already_t_wise;
};

void *CDCLCASampler::pthread_func2(void* arg){
    struct para2 *p = (struct para2 *)arg;
    CDCLSolver::Solver *cdcl_solver = p->cdcl_solver2;
    CDCLCASampler *th = p->th;
    long long *num_tuple_all_exact_ = p->num_tuple_all_exact_;
    long long *invalid_tuple_num = p->invalid_tuple_num;
    vector<vector<int> > *uncovered_possible_solutions = p->uncovered_possible_solutions;
    vector<vector<int> > *uncovered_tuples = p->uncovered_tuples;
    vector<int> *as_backbone = p->as_backbone;
    int idx = p->idx;
    int num_var_ = p->num_var_;
    int parallel_num = p->parallel_num;
    bool simplify = p->simplify;
    SimpleBitSet *already_t_wise = p->already_t_wise;

    int cnt = 0;

    for (int i = 0; i < num_var_ - 1; ++i){
        for (int v_i = 0; v_i < 2; ++v_i){
            if (as_backbone->at(i) != -1 && v_i != as_backbone->at(i))continue;
            for (int j = i + 1; j < num_var_; ++j){
                for (int v_j = 0; v_j < 2; ++v_j){
                    if (as_backbone->at(j) != -1 && v_j != as_backbone->at(j))continue;
                    long long index_tuple = th->Get2TupleMapIndex(i, v_i, j, v_j);
                    if (!already_t_wise->get(index_tuple)){
                        if(cnt++ % parallel_num == idx){
                            bool flag = true;
                            if (simplify){
                                cdcl_solver->add_assumption(i, v_i);
                                cdcl_solver->add_assumption(j, v_j);
                                bool res = cdcl_solver->solve();
                                if (!res){
                                    ++*num_tuple_all_exact_;
                                    ++*invalid_tuple_num;
                                    flag = false;
                                }
                                cdcl_solver->clear_assumptions();
                            }
                            // /* Not save uncovered tuples.
                            if (flag){
                                uncovered_tuples->emplace_back(vector<int>{v_i ? (i+1):(-i-1), v_j ? (j+1):(-j-1)});
                            }
                            // */
                        }    
                    }
                }
            }
        }
    }
    free(p);
    pthread_exit(NULL);
};

void CDCLCASampler::find_uncovered_tuples(bool simplify){
    pthread_t tid[parallel_num] = {0};
    CDCLSolver::Solver *cdcl_solver_list[parallel_num] = {cdcl_solver};
    for (int i = 1; i < parallel_num; i++){
        cdcl_solver_list[i] = new CDCLSolver::Solver;
        cdcl_solver_list[i]->read_clauses(num_var_, clauses);
    }
    vector< vector< vector<int> > > possible_s(parallel_num);
    vector< vector< vector<int> > > possible_t(parallel_num);
    vector<long long> t_num(parallel_num);
    vector<long long> it_num(parallel_num);

    for (int i = 0; i < num_var_ - 1; ++i){
        for (int v_i = 0; v_i < 2; ++v_i){
            if (as_backbone[i] != -1 && v_i != as_backbone[i]){
                num_tuple_all_exact_ -= 2ll * (num_var_ - i - 1);
                invalid_tuple_num += 2ll * (num_var_ - i - 1);
                continue;
            }
            for (int j = i + 1; j < num_var_; ++j){
                for (int v_j = 0; v_j < 2; ++v_j){
                    if (as_backbone[j] != -1 && v_j != as_backbone[j]){
                        --num_tuple_all_exact_;
                        ++invalid_tuple_num;
                        continue;
                    }
                    if(parallel_num == 1){
                        long long index_tuple = Get2TupleMapIndex(i, v_i, j, v_j);
                        if (!already_t_wise.get(index_tuple)){
                            bool flag = true;
                            if (simplify){
                                cdcl_solver->add_assumption(i, v_i);
                                cdcl_solver->add_assumption(j, v_j);
                                bool res = cdcl_solver->solve();
                                if (!res){
                                    --num_tuple_all_exact_;
                                    ++invalid_tuple_num;
                                    flag = false;
                                } 
                                cdcl_solver->clear_assumptions();
                            }
                            // /*  Not save uncovered tuples.
                            if (flag){
                                uncovered_tuples.emplace_back(vector<int>{v_i ? (i+1):(-i-1), v_j ? (j+1):(-j-1)});
                            }
                            // */
                        }
                    }
                    
                }
            }
        }
    }
    if(parallel_num != 1){
        for (int i = 0; i < parallel_num; i++){
            int *p = (int*)malloc(sizeof(*p));
            *p = i;
            struct para2 *myp = (struct para2*)malloc(sizeof(struct para2));
            myp->cdcl_solver2 = cdcl_solver_list[*p];
            myp->idx = *p;
            myp->num_var_ = num_var_;
            myp->parallel_num = parallel_num;
            myp->num_tuple_all_exact_ = &t_num[i];
            myp->invalid_tuple_num = &it_num[i];
            myp->as_backbone = &as_backbone;
            myp->already_t_wise = &already_t_wise;
            myp->uncovered_possible_solutions = &(possible_s[i]);
            myp->uncovered_tuples = &(possible_t[i]);
            myp->simplify = simplify;
            myp->th = this;
            pthread_create(&tid[*p],NULL,pthread_func2,(void*)myp);
            free(p);
        }

        for (int i = 0; i < parallel_num; i++){
            pthread_join(tid[i],NULL);
            num_tuple_all_exact_ -= t_num[i];
            invalid_tuple_num += it_num[i];
            for(auto tc: possible_s[i]){
                uncovered_possible_solutions.emplace_back(tc);
            }
            for(auto tuple: possible_t[i]){
                uncovered_tuples.emplace_back(tuple);
            }
        }
        for (int i = 1; i < parallel_num; i++)delete(cdcl_solver_list[i]);
    }
    cout << "covered:" << already_t_wise.count() << endl;
    cout << "unc:" << uncovered_tuples.size() << endl;
    cout << "invalid:" << invalid_tuple_num << endl;
}

void *CDCLCASampler::pthread_func5(void* arg){
    struct para2 *p = (struct para2 *)arg;
    CDCLSolver::Solver *cdcl_solver = p->cdcl_solver2;
    CDCLCASampler *th = p->th;
    long long *num_tuple_all_exact_ = p->num_tuple_all_exact_;
    long long *invalid_tuple_num = p->invalid_tuple_num;
    vector<vector<int> > *uncovered_possible_solutions = p->uncovered_possible_solutions;
    vector<vector<int> > *uncovered_tuples = p->uncovered_tuples;
    vector<int> *as_backbone = p->as_backbone;
    int idx = p->idx;
    int num_var_ = p->num_var_;
    int parallel_num = p->parallel_num;
    bool simplify = p->simplify;
    SimpleBitSet *already_t_wise = p->already_t_wise;

    int cnt = 0;

    for (int i = 0; i < num_var_ - 1; ++i){
        for (int v_i = 0; v_i < 2; ++v_i){
            if (as_backbone->at(i) != -1 && v_i != as_backbone->at(i))continue;
            for (int j = i + 1; j < num_var_; ++j){
                for (int v_j = 0; v_j < 2; ++v_j){
                    if (as_backbone->at(j) != -1 && v_j != as_backbone->at(j))continue;
                    long long index_tuple = th->Get2TupleMapIndex(i, v_i, j, v_j);
                    if (!already_t_wise->get(index_tuple)){
                        if(cnt++ % parallel_num == idx){
                            bool flag = true;
                            if (simplify){
                                cdcl_solver->add_assumption(i, v_i);
                                cdcl_solver->add_assumption(j, v_j);
                                bool res = cdcl_solver->solve();
                                if (!res){
                                    ++*num_tuple_all_exact_;
                                    ++*invalid_tuple_num;
                                    flag = false;
                                }
                                else {
                                    vector<int> tc(num_var_, 0);
                                    cdcl_solver->get_solution(tc);
                                    uncovered_possible_solutions->emplace_back(tc);
                                }
                                cdcl_solver->clear_assumptions();
                            }
                            if (flag){
                                uncovered_tuples->emplace_back(vector<int>{v_i ? (i+1):(-i-1), v_j ? (j+1):(-j-1)});
                            }
                            // */
                        }    
                    }
                }
            }
        }
    }
    free(p);
    pthread_exit(NULL);
};

void CDCLCASampler::find_uncovered_tuples2(bool simplify){
    pthread_t tid[parallel_num] = {0};
    CDCLSolver::Solver *cdcl_solver_list[parallel_num] = {cdcl_solver};
    for (int i = 1; i < parallel_num; i++){
        cdcl_solver_list[i] = new CDCLSolver::Solver;
        cdcl_solver_list[i]->read_clauses(num_var_, clauses);
    }
    vector< vector< vector<int> > > possible_s(parallel_num);
    vector< vector< vector<int> > > possible_t(parallel_num);
    vector<long long> t_num(parallel_num);
    vector<long long> it_num(parallel_num);

    for (int i = 0; i < num_var_ - 1; ++i){
        for (int v_i = 0; v_i < 2; ++v_i){
            if (as_backbone[i] != -1 && v_i != as_backbone[i]){
                num_tuple_all_exact_ -= 2ll * (num_var_ - i - 1);
                invalid_tuple_num += 2ll * (num_var_ - i - 1);
                continue;
            }
            for (int j = i + 1; j < num_var_; ++j){
                for (int v_j = 0; v_j < 2; ++v_j){
                    if (as_backbone[j] != -1 && v_j != as_backbone[j]){
                        --num_tuple_all_exact_;
                        ++invalid_tuple_num;
                        continue;
                    }
                    if(parallel_num == 1){
                        long long index_tuple = Get2TupleMapIndex(i, v_i, j, v_j);
                        if (!already_t_wise.get(index_tuple)){
                            bool flag = true;
                            if (simplify){
                                cdcl_solver->add_assumption(i, v_i);
                                cdcl_solver->add_assumption(j, v_j);
                                bool res = cdcl_solver->solve();
                                if (!res){
                                    --num_tuple_all_exact_;
                                    ++invalid_tuple_num;
                                    flag = false;
                                } 
                                else {
                                    vector<int> tc(num_var_, 0);
                                    get_cadical_solution(tc);
                                    uncovered_possible_solutions.emplace_back(tc);
                                }
                                cdcl_solver->clear_assumptions();
                            }
                            // /*  Not save uncovered tuples.
                            if (flag){
                                uncovered_tuples.emplace_back(vector<int>{v_i ? (i+1):(-i-1), v_j ? (j+1):(-j-1)});
                            }
                            // */
                        }
                    }
                    
                }
            }
        }
    }
    if(parallel_num != 1){
        for (int i = 0; i < parallel_num; i++){
            int *p = (int*)malloc(sizeof(*p));
            *p = i;
            struct para2 *myp = (struct para2*)malloc(sizeof(struct para2));
            myp->cdcl_solver2 = cdcl_solver_list[*p];
            myp->idx = *p;
            myp->num_var_ = num_var_;
            myp->parallel_num = parallel_num;
            myp->num_tuple_all_exact_ = &t_num[i];
            myp->invalid_tuple_num = &it_num[i];
            myp->as_backbone = &as_backbone;
            myp->already_t_wise = &already_t_wise;
            myp->uncovered_possible_solutions = &(possible_s[i]);
            myp->uncovered_tuples = &(possible_t[i]);
            myp->simplify = simplify;
            myp->th = this;
            pthread_create(&tid[*p],NULL,pthread_func5,(void*)myp);
        }

        for (int i = 0; i < parallel_num; i++){
            pthread_join(tid[i],NULL);
            num_tuple_all_exact_ -= t_num[i];
            invalid_tuple_num += it_num[i];
            for(auto tc: possible_s[i]){
                uncovered_possible_solutions.emplace_back(tc);
            }
            for(auto tuple: possible_t[i]){
                uncovered_tuples.emplace_back(tuple);
            }
        }
        for (int i = 1; i < parallel_num; i++)delete(cdcl_solver_list[i]);
    }
    
    cout << "unc:" << uncovered_tuples.size() << endl;
    cout << "invalid:" << invalid_tuple_num << endl;
}

void CDCLCASampler::get_cadical_solution(vector<int>& tc){
    cdcl_solver->get_solution(tc);
}

void CDCLCASampler::choose_final_plain()
{
    find_uncovered_tuples(true);

    size_t uncovered_size = uncovered_tuples.size();
    size_t ftc_size = uncovered_possible_solutions.size(), i = 0;
    while (i < ftc_size && uncovered_size > 0){
        long long tuple_index = Get2TupleMapIndex(
            abs(uncovered_tuples[i][0]) - 1, uncovered_tuples[i][0] < 0 ? 0: 1, 
            abs(uncovered_tuples[i][1]) - 1, uncovered_tuples[i][1] < 0 ? 0: 1);
        if (already_t_wise.get(tuple_index)){
            ++i;
            continue;
        }

        testcase_set_.emplace_back(uncovered_possible_solutions[i]);
        ++num_generated_testcase_;
        (this->*p_update_tuple_info_)();
        cout << num_generated_testcase_ << ": " << num_tuple_ << endl;
        ++i;
    }
}

void CDCLCASampler::choose_final_random_contiguous_solving(bool simplify)
{
    find_uncovered_tuples(simplify);

    vector<int> tupleids(uncovered_tuples.size(), 0);
    iota(tupleids.begin(), tupleids.end(), 0);

    shuffle(tupleids.begin(), tupleids.end(), rnd_file_id_gen_);

    vector<int> tc(num_var_, 0);
    size_t uncovered_size = uncovered_tuples.size(), i = 0;
    for (size_t i = 0; i < uncovered_size; ){
        long long tuple_index = Get2TupleMapIndex(
            abs(uncovered_tuples[tupleids[i]][0]) - 1, uncovered_tuples[tupleids[i]][0] < 0 ? 0: 1, 
            abs(uncovered_tuples[tupleids[i]][1]) - 1, uncovered_tuples[tupleids[i]][1] < 0 ? 0: 1);
        if (already_t_wise.get(tuple_index)){
            ++i;
            continue;
        }
        
        size_t j = i;
        while (j < uncovered_size){
            for (size_t k = i; k <= j; ++k){
                cdcl_solver->add_assumption(uncovered_tuples[tupleids[k]][0]);
                cdcl_solver->add_assumption(uncovered_tuples[tupleids[k]][1]);
            }
            bool res = cdcl_solver->solve();
            if (!res){
                break;
            } else {
                get_cadical_solution(tc);
                ++j;
            }
            cdcl_solver->clear_assumptions();
        }
        if (j == i){
            --num_tuple_all_exact_;
            ++i;
        } else {
            testcase_set_.emplace_back(tc);
            ++num_generated_testcase_;
            (this->*p_update_tuple_info_)();
            cout << num_generated_testcase_ << ": " << num_tuple_ << endl;
            i = j;
        }
    }
}

void CDCLCASampler::choose_final_solution_modifying(bool shf)
{
    find_uncovered_tuples(true);

    vector<int> tupleids(uncovered_tuples.size(), 0);
    vector<int> tmp_tupleids(uncovered_tuples.size(), 0);
    iota(tupleids.begin(), tupleids.end(), 0);

    if (shf){
        shuffle(tupleids.begin(), tupleids.end(), rnd_file_id_gen_);
    }

    vector<int> tc(num_var_, 0);
    vector<bool> asgn_fixed(num_var_, false);
    vector<int> clause_truecount(num_clauses_, 0);
    size_t uncovered_size = uncovered_tuples.size();

    auto flip_var = [&](int x, int o){
        int v = abs(x);
        if (asgn_fixed[v - 1]){
            return ;
        }
        int deltapos = o, deltaneg = -o;
        if (x < 0) deltapos = -o, deltaneg = o;
        for (int cl: pos_in_cls[v]){
            clause_truecount[cl] += deltapos;
        }
        for (int cl: neg_in_cls[v]){
            clause_truecount[cl] += deltaneg;
        }
    };

    while (uncovered_size > 0){
        for (int i = 0; i < num_clauses_; ++i){
            clause_truecount[i] = 0;
        }
        int t0 = tupleids[0];
        for (int i = 0; i < num_var_; ++i){
            tc[i] = uncovered_possible_solutions[t0][i];
            if (tc[i] == 0){
                for (int cl: neg_in_cls[i + 1]){
                    ++clause_truecount[cl];
                }
            } else {
                for (int cl: pos_in_cls[i + 1]){
                    ++clause_truecount[cl];
                }
            }
        }
        for (int x: uncovered_tuples[t0]){
            asgn_fixed[abs(x) - 1] = true;
        }

        for (int i = 1; i < uncovered_size; ++i){
            bool ok = true;
            for (int x: uncovered_tuples[tupleids[i]]){
                int v = abs(x);
                if (asgn_fixed[v - 1] && (tc[v - 1] == 0) != (x < 0)){
                    ok = false;
                    break;
                }
            }
            if (!ok) continue;
            for (int x: uncovered_tuples[tupleids[i]]){
                flip_var(x, 1);
            }
            for (int i = 0; i < num_clauses_; ++i){
                if (clause_truecount[i] == 0){
                    ok = false;
                    break;
                }
            }
            if (!ok){
                for (int x: uncovered_tuples[tupleids[i]]){
                    flip_var(x, -1);
                }
                continue;
            }
            for (int x: uncovered_tuples[tupleids[i]]){
                int v = abs(x);
                asgn_fixed[v - 1] = true;
                tc[v - 1] = (x > 0) ? 1: 0;
            }
        }

        testcase_set_.emplace_back(tc);
        ++num_generated_testcase_;
        (this->*p_update_tuple_info_)();
        cout << num_generated_testcase_ << ": " << num_tuple_ << endl;
        
        size_t new_uncovered_size = 0;
        for (int i = 0; i < uncovered_size; ++i){
            long long tuple_index = Get2TupleMapIndex(
                abs(uncovered_tuples[tupleids[i]][0]) - 1, uncovered_tuples[tupleids[i]][0] < 0 ? 0: 1, 
                abs(uncovered_tuples[tupleids[i]][1]) - 1, uncovered_tuples[tupleids[i]][1] < 0 ? 0: 1);
            if (!already_t_wise.get(tuple_index)){
                tmp_tupleids[new_uncovered_size++] = tupleids[i];
            }
        }
        uncovered_size = new_uncovered_size;
        swap(tupleids, tmp_tupleids);
    }
}

void CDCLCASampler::clear_final()
{
    cout << endl << "c Clear final: fix-up all remaining tuples ..." << endl;
    
    if(num_combination_all_possible_*4 > 1000000){
        num_tuple_all_possible_ = num_combination_all_possible_ * 4;
        already_t_wise = SimpleBitSet(num_tuple_all_possible_);
        num_tuple_ = 0;

        for (int k = 0; k < num_generated_testcase_; k++){
            for (int i = 0; i < num_var_ - 1; i++){
                for (int j = i + 1; j < num_var_; j++){
                    long long index_tuple = Get2TupleMapIndex(i, testcase_set_[k][i], j, testcase_set_[k][j]);
                    if (!already_t_wise.get(index_tuple)){
                        already_t_wise.set(index_tuple);
                        num_tuple_++;
                    }
                }
            }
        }

    }

    num_tuple_all_exact_ = num_tuple_all_possible_;

    cdcl_solver = new CDCLSolver::Solver;
    cdcl_solver->read_clauses(num_var_, clauses);

    uncovered_tuples.clear();
    uncovered_possible_solutions.clear();

    (this->*p_choose_final)();
    // find_uncovered_tuples(true);

    delete cdcl_solver;

    coverage_tuple_ = double(num_tuple_) / num_tuple_all_exact_;

    cout << "c All possible 2-tuple number: " << num_tuple_all_exact_ << endl;
    cout << "c 2-tuple coverage: " << coverage_tuple_ << endl;
}

void CDCLCASampler::clear_final2()
{
    cout << endl << "c Clear final: fix-up all remaining tuples ..." << endl;
    
    if(num_combination_all_possible_*4 > 1000000){
        num_tuple_all_possible_ = num_combination_all_possible_ * 4;
        already_t_wise = SimpleBitSet(num_tuple_all_possible_);
        num_tuple_ = 0;

        for (int k = 0; k < num_generated_testcase_; k++){
            for (int i = 0; i < num_var_ - 1; i++){
                for (int j = i + 1; j < num_var_; j++){
                    long long index_tuple = Get2TupleMapIndex(i, testcase_set_[k][i], j, testcase_set_[k][j]);
                    if (!already_t_wise.get(index_tuple)){
                        already_t_wise.set(index_tuple);
                        num_tuple_++;
                    }
                }
            }
        }

    }

    num_tuple_all_exact_ = num_tuple_all_possible_;

    cdcl_solver = new CDCLSolver::Solver;
    cdcl_solver->read_clauses(num_var_, clauses);

    uncovered_tuples.clear();
    uncovered_possible_solutions.clear();

    find_uncovered_tuples2(true);

    size_t uncovered_size = uncovered_tuples.size();
    size_t ftc_size = uncovered_possible_solutions.size(), i = 0;
    while (i < ftc_size && uncovered_size > 0){
        long long tuple_index = Get2TupleMapIndex(
            abs(uncovered_tuples[i][0]) - 1, uncovered_tuples[i][0] < 0 ? 0: 1, 
            abs(uncovered_tuples[i][1]) - 1, uncovered_tuples[i][1] < 0 ? 0: 1);
        if (already_t_wise.get(tuple_index)){
            ++i;
            continue;
        }

        testcase_set_.emplace_back(uncovered_possible_solutions[i]);
        ++num_generated_testcase_;
        (this->*p_update_tuple_info_)();
        cout << num_generated_testcase_ << ": " << num_tuple_ << endl;
        ++i;
    }

    delete cdcl_solver;

    coverage_tuple_ = double(num_tuple_) / num_tuple_all_exact_;

    cout << "c All possible 2-tuple number: " << num_tuple_all_exact_ << endl;
    cout << "c 2-tuple coverage: " << coverage_tuple_ << endl;
}

void CDCLCASampler::read_cnf_header(ifstream& ifs, int& nvar, int& nclauses){
    string line;
    istringstream iss;
    int this_num_var;
    
    while (getline(ifs, line)){
        if (line.substr(0, 1) == "c")
            continue;
        else if (line.substr(0, 1) == "p"){
            string tempstr1, tempstr2;
            iss.clear();
            iss.str(line);
            iss.seekg(0, ios::beg);
            iss >> tempstr1 >> tempstr2 >> this_num_var >> nclauses;
            if (nvar < this_num_var)
                nvar = this_num_var;
            break;
        }
    }
}

bool CDCLCASampler::check_no_clauses(){
    ifstream fin(cnf_file_path_.c_str());
    if (!fin.is_open()) return true;

    int num_clauses_original;
    read_cnf_header(fin, num_var_, num_clauses_original);

    fin.close();
    return num_clauses_original <= 0;
}

bool CDCLCASampler::read_cnf(){
    ifstream fin(cnf_file_path_.c_str());
    if (!fin.is_open()) return false;

    read_cnf_header(fin, num_var_, num_clauses_);

    if (num_var_ <= 0 || num_clauses_ < 0){
        fin.close();
        return false;
    }

    pos_in_cls.resize(num_var_ + 1, vector<int>());
    neg_in_cls.resize(num_var_ + 1, vector<int>());
    clauses.resize(num_clauses_);
    as_backbone.resize(num_var_, -1);

    for (int c = 0; c < num_clauses_; ++c)
    {
        int cur_lit;
        fin >> cur_lit;
        while (cur_lit != 0)
        {
            int v = abs(cur_lit);
            if (cur_lit > 0) pos_in_cls[v].push_back(c);
            else neg_in_cls[v].push_back(c);
            clauses[c].emplace_back(cur_lit);
            fin >> cur_lit;
        }

        if ((int) clauses[c].size() == 1){
            int bv = abs(clauses[c][0]) - 1;
            as_backbone[bv] = clauses[c][0] > 0 ? 1: 0;
        }
    }

    fin.close();

    return true;
}

void CDCLCASampler::SetUpperLimit(std::string answer_file_path){
    FILE *in = fopen(answer_file_path.c_str(), "r");
    int ret = fscanf(in, "%lld", &upperlimit);
    use_upperlimit = true;
    fclose(in);
}

void CDCLCASampler::stage_change(int cur_phase){
    sample_dim_ = cur_phase;
    tuple_sampler(sample_dim_, sample_cnt_, tp_sample);

    already_t_wise = SimpleBitSet(sample_cnt_);
    num_tuple_ = 0;
    num_tuple_all_possible_ = sample_cnt_;

    p_update_tuple_info_ = &CDCLCASampler::UpdateXTupleInfo;
    p_get_gain = &CDCLCASampler::get_gain_by_samples;
    
    pq.clear();
    pq_idx.clear();

    sample_uncovered.clear();

    for (int i = 0; i < sample_cnt_; ++i){
        bool ok = false;
        for (int j = 0; j < num_generated_testcase_; ++j){
            if (check_tuple_in_testcase(tp_sample[i], testcase_set_[j])){
                ok = true;
                break;
            }
        }
        if (!ok){
            sample_uncovered.emplace_back(i);
        } else {
            ++num_tuple_;
        }
    }
}

void CDCLCASampler::tuple_sampler(int dim, int tuplecnt, vector<vector<int> >& tp_sample)
{
    tp_sample.clear();

    vector<int> tp(dim * 2, 0);
    vector<int> vec(num_var_, 0);
    std::iota(vec.begin(), vec.end(), 1);

    for (int i = 0; i < tuplecnt; ++i){
        std::shuffle(vec.begin(), vec.end(), rng_2);
        for (int j = 0; j < dim; ++j){
            tp[j << 1] = vec[j] - 1;
            if (rng_2() % 2) tp[j << 1 | 1] = 1;
            else tp[j << 1 | 1] = 0;
        }            
        tp_sample.emplace_back(tp);
    }
}

void CDCLCASampler::UpdateXTupleInfo()
{
    
    if (selected_candidate_bitset_.init_iter()){
        do {
            size_t tp_id = selected_candidate_bitset_.iter_get();
            already_t_wise.set(tp_id);
            ++num_tuple_;
        } while (selected_candidate_bitset_.iter_next());
    }

    size_t uncovered_cnt = sample_uncovered.size();
    for (size_t i = 0; i + 1 < uncovered_cnt; ){
        if (selected_candidate_bitset_.get(sample_uncovered[i])){
            swap(sample_uncovered[i], sample_uncovered[uncovered_cnt - 1]);
            sample_uncovered.pop_back();
            --uncovered_cnt;
        } else ++i;
    }
    if (uncovered_cnt > 0 &&
        selected_candidate_bitset_.get(sample_uncovered.back())){
        sample_uncovered.pop_back();
    }
}

bool CDCLCASampler::check_tuple_in_testcase(const vector<int>& utp, const vector<int>& asgn){
    for (int i = 0; i < sample_dim_; ++i){
        if (asgn[utp[i << 1]] != utp[i << 1 | 1]){
            return false;
        }
    }
    return true;
}

SimpleBitSet CDCLCASampler::get_gain_by_samples(const vector<int>& asgn){
    SimpleBitSet res(num_tuple_all_possible_);
    for (int ii: sample_uncovered){
        if (check_tuple_in_testcase(tp_sample[ii], asgn)) res.set(ii);
    }
    return res;
}