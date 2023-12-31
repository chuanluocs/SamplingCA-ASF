COMPILER = g++
CFLAGS = -O3 -std=c++11 -lpthread  #-static -g -O3

PRE_CFLAGS = ${CFLAGS} -c
TARGET = SamplingCA-ASF

SRC_DIR = src

BIN_DIR = bin

MERSENNE = mersenne
MERSENNE_TARGET = ${SRC_DIR}/${MERSENNE}.o
MERSENNE_CC_FILE = ${SRC_DIR}/${MERSENNE}.cc
MERSENNE_H_FILE = ${SRC_DIR}/${MERSENNE}.h
MERSENNE_SOURCE_FILES = ${MERSENNE_H_FILE} ${MERSENNE_CC_FILE}

PBOCCSATSOLVER = pboccsatsolver
PBOCCSATSOLVER_TARGET = ${SRC_DIR}/${PBOCCSATSOLVER}.o
PBOCCSATSOLVER_CPP_FILE = ${SRC_DIR}/${PBOCCSATSOLVER}.cpp
PBOCCSATSOLVER_H_FILE = ${SRC_DIR}/${PBOCCSATSOLVER}.h
PBOCCSATSOLVER_SOURCE_FILES = ${SOLVER_H_FILE} ${SOLVER_CPP_FILE}

CDCLCASAMPLER = cdclcasampler
CDCLCASAMPLER_TARGET = ${SRC_DIR}/${CDCLCASAMPLER}.o
CDCLCASAMPLER_CPP_FILE = ${SRC_DIR}/${CDCLCASAMPLER}.cpp
CDCLCASAMPLER_H_FILE = ${SRC_DIR}/${CDCLCASAMPLER}.h
CDCLCASAMPLER_SOURCE_FILES = ${CDCLCASAMPLER_H_FILE} ${CDCLCASAMPLER_CPP_FILE}

EXT_MINISAT_TARGET = minisat_ext/Solver.o minisat_ext/Ext.o minisat_ext/BlackBoxSolver.o
EXT_MINISAT_SOURCE_FILES = minisat_ext/Solver.cc minisat_ext/Solver.h minisat_ext/Ext.h minisat_ext/Ext.cc minisat_ext/BlackBoxSolver.h minisat_ext/BlackBoxSolver.cc

TARGET_FILES =	${EXT_MINISAT_TARGET} \
				${MERSENNE_TARGET} \
				${PBOCCSATSOLVER_TARGET} \
				${CDCLCASAMPLER_TARGET} \
				
MAIN_SOURCE_FILE = ${SRC_DIR}/main.cpp

UPDATE = update
CLEAN = clean
CLEANUP = cleanup

all: ${TARGET_FILES} ${TARGET} ${UPDATE} ${CLEAN}

${MERSENNE_TARGET}: ${MERSENNE_SOURCE_FILES}
	${COMPILER} ${PRE_CFLAGS} ${MERSENNE_CC_FILE} -o ${MERSENNE_TARGET}

${PBOCCSATSOLVER_TARGET}: ${PBOCCSATSOLVER_SOURCE_FILES}
	${COMPILER} ${PRE_CFLAGS} ${PBOCCSATSOLVER_CPP_FILE} -o ${PBOCCSATSOLVER_TARGET}

${CDCLCASAMPLER_TARGET}: ${CDCLCASAMPLER_SOURCE_FILES}
	${COMPILER} ${PRE_CFLAGS} ${CDCLCASAMPLER_CPP_FILE} -o ${CDCLCASAMPLER_TARGET}

${EXT_MINISAT_TARGET}: ${EXT_MINISAT_SOURCE_FILES}
	cd minisat_ext; make -f Makefile extminisat; cd ..

${TARGET}: ${MAIN_SOURCE_FILE} ${TARGET_FILES}
	${COMPILER} ${CFLAGS} ${MAIN_SOURCE_FILE} ${TARGET_FILES} -o ${TARGET} -lpthread

${UPDATE}:
	chmod +x -R ${BIN_DIR}/

${CLEAN}:
	rm -f *~
	rm -f ${SRC_DIR}/*.o
	rm -f ${SRC_DIR}/*~
	rm -f minisat/utils/*.or
	rm -f minisat/utils/*.o
	rm -f ${EXT_MINISAT_TARGET}
	rm -f minisat_ext/depend.mk

${CLEANUP}: ${CLEAN}
	rm -f ${TARGET}
