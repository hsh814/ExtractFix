#include<stdlib.h>
#include<stdint.h>
#include<stdio.h>

#include<klee/klee.h>

#define AVERROR_INVALIDDATA -1


static int decode_dds1(int segments, uint8_t *frame, int width, int height)
{
	klee_make_symbolic(&width, sizeof(width), "width");

    const uint8_t *frame_start = frame;
    const uint8_t *frame_end   = frame + width * height;
    int i, v, offset, count;
	

	//klee_make_symbolic(&height, sizeof(height), "height");
	//klee_make_symbolic(&frame, sizeof frame, "frame");
	//klee_make_symbolic(&frame_end, sizeof frame_end, "frame_end");

	if (frame_end - frame < width + 3)
	    return AVERROR_INVALIDDATA;
	
	//klee_make_symbolic(&width, sizeof(width), "width");
	
	frame += 2;
	klee_assume(frame + width + 1 < frame_end);
	frame[width + 1] =  '0'; // width + 1 < 6
	
	frame += 2;
	
    return 0;
}

void* x_malloc(int n){
	void* res = malloc(n);
	return res;
}


int main(){
	int size = 6;
	//SIZE = size;
	uint8_t* frame = (uint8_t*) x_malloc(size);
	
  	//klee_make_symbolic(frame, sizeof(frame), "frame");
	//klee_assume(frame[size - 1] == 0);
	int height = 2;
	int width = 1 + height;
	decode_dds1(1, frame, width, 2);
	
	return 0;
}
