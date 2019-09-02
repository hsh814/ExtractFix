// A C program to demonstrate divide by zero
#include <stdio.h> 
#include <string.h> 

int main(int argc, char *argv[]) 
{ 
    // a prompt how to execute the program. 
    int a = atoi(argv[1]);
    int b = atoi(argv[2]);
    float ret = a/b;
    printf("a=%d b=%d, ret=%f\n", a, b, ret);
    if (ret < 0)
        return -1;
  
    return ret; 
} 

int* main3(){
    return NULL;
}
