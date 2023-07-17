# *SamplingCA-ASF*: Sampling-based Pairwise Testing with Approximated Scoring Function

*SamplingCA-ASF* is an effective and efficient sampling-based approach for pairwise testing of highly configurable software systems. This repository includes the implementation of *SamplingCA-ASF*, the testing instances adopted in the experiments and the experimental results. 

## Instructions for Running *SamplingCA-ASF*

After building *SamplingCA-ASF*, users may run it with the following command: 

```
./SamplingCA-ASF -input_cnf_path [INSTANCE_PATH] <optional_parameters> <optional_flags>
```

`-input_cnf_path` is the only required parameter. As mentioned above, the input file for *SamplingCA-ASF* must be in [Dimacs format](http://www.satcompetition.org/2011/format-benchmarks2011.html). The directory named `cnf_instances/` contains 2 testing instances, which can be taken as input. Users may also use [FeatureIDE](https://github.com/FeatureIDE/FeatureIDE/) to generate input files from existing configurable systems. 

For the optional parameters, we list them as follows. 

| Parameter | Allowed Values | Default Value | Description | 
| - | - | - | - |
| `-output_testcase_path` | string | `./[INPUT_CNF_NAME]_testcase_set.txt` | path to which the generated PCA is saved |
| `-seed` | integer | 1 | random seed | 
| `-k` | positive integer | 100 | the number of candidates per round | 

## Example Command for Running *SamplingCA-ASF*

```
./SamplingCA-ASF -input_cnf_path cnf_instances/linux.cnf -seed 1 -k 100
```

The command above calls *SamplingCA-ASF* to solve the instance `cnf_instances/linux.cnf` by setting the random seed to 1 and the number of candidate test cases per iteration round of the sampling phase to 100. The generated PCA will be saved in `./linux_testcase_set.txt`. 

## Experimental Results

For the generated test cases of the Automotive02 and Linux instances, users can download them from the following links.
- [Automotive02_V4](https://drive.google.com/file/d/15A5hQho7bbUcDhdhyiApj4a_HbjEftXA/view?usp=sharing): The generated test cases for Automotive02 (Version: V4).
- [Linux](https://drive.google.com/file/d/12cea06EUW6Nf5Js6RjVylrtFnUUyv6DQ/view?usp=sharing): The generated test cases for Linux.
