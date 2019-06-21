all: clean SymbolicInserter run

SymbolicInserter:
	clang++ Metedata_extractor.cpp SymbolicInserter.cpp -c -g -O0 -fPIC `llvm-config --cxxflags` `llvm-config --includedir`
	clang++ -o SymbolicInserter.so SymbolicInserter.o Metedata_extractor.o -shared `llvm-config --ldflags`
	
run:
	opt -S -load=./SymbolicInserter.so -symbolic_inserter -insert_function 'main' -insert_index '4' ../../test/get_sign.bc
	#opt -S -load=./SymbolicInserter.so -symbolic_inserter -crash_location '/ffmpeg.bc:30' ../../test/ffmpeg.bc

clean:
	rm -f *.so *.o SymbolicInserter.dwo

