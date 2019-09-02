// A C program to demonstrate buffer overflow 
#include <stdio.h> 
#include <string.h> 
#include <stdlib.h> 
  
int main(int argc, char *argv[]) 
{ 
       // Reserve 5 byte of buffer plus the terminating NULL. 
       char buffer[5]; 
  
       // a prompt how to execute the program... 
       if (argc < 2) 
       { 
              printf("strcpy() NOT executed....\n"); 
              printf("Syntax: %s <characters>\n", argv[0]); 
              exit(0); 
       } 
  
       // copy the user input to mybuffer
       int i = 0;
       char* content = argv[1];
       int content_size = strlen(content);
       printf("content_size = %d\n", content_size);
       for (i; i<content_size; i++)
           buffer[i] = content[i];
       printf("buffer content= %s\n", buffer); 
  
       // you may want to try strcpy_s() 
       printf("strcpy() executed...\n"); 
  
       return 0; 
} 
