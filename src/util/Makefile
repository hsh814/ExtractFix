all: clean SymbolicInserter run

SymbolicInserter:
	clang++ SymbolicInserter.cpp -c -g -O0 -fPIC `llvm-config --cxxflags` `llvm-config --includedir`
	clang++ -o SymbolicInserter.so SymbolicInserter.o -shared `llvm-config --ldflags`
	
run:
	opt -S -load=./SymbolicInserter.so -symbolic_inserter -insert_function 'main' -insert_index '4' ../../test/get_sign.bcz
	#opt -S -load=./SymbolicInserter.so -symbolic_inserter -crash_location '/ffmpeg.bc:30' ../../test/ffmpeg.bc

clean:
	rm -f SymbolicInserter.so SymbolicInserter.o SymbolicInserter.dwo

FuncTracer:
	clang++ FuncTracer.cpp -c -g -O0 -fPIC `llvm-config --cxxflags` `llvm-config --includedir`
	clang++ -o FuncTracer.so FuncTracer.o -shared `llvm-config --ldflags`

runTracer:
	opt -S -load=/home/nightwish/workspace/bug_repair/crash-free-fix/src/util/FuncTracer.so -func_tracer ../../test/get_sign.bc
