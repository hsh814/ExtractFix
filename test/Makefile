ffmpeg: ffmpeg.c
	clang -I ../src/klee/include -emit-llvm -c -g -O0 -Xclang -disable-O0-optnone ffmpeg.c

ffmpeg-r: ffmpeg.c
	clang -I ../src/klee/include -emit-llvm -S -g -O0 -Xclang -disable-O0-optnone ffmpeg.c

get_sign: get_sign.c
	clang -I ../src/klee/include -emit-llvm -c -g -O0 -Xclang -disable-O0-optnone get_sign.c

clean:
	rm -rf *.ll *bc
