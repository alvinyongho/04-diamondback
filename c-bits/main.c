#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CONST_TRUE 0xFFFFFFFF
#define CONST_FALSE 0x7FFFFFFF


extern int our_code_starts_here() asm("our_code_starts_here");
extern int print(int val) asm("print");

extern void error(int code, int v) asm("error");

void error(int code, int v) {

  if (code == 0){
    fprintf(stderr, "Error: expected a number but got %#010x\n", v);
  } else if (code == 1){
    fprintf(stderr, "Error: expected a boolean but got %#010x\n", v);
  } else if (code == 2){
    fprintf(stderr, "Error: arithmetic overflow");
  }
  exit(1);
}


int print(int val) {
  if(val & 0x00000001 ^ 0x00000001) {
    printf("%d\n", val >> 1);
  }
  else if(val == 0xFFFFFFFF) {
    printf("true\n");
  }
  else if(val == 0x7FFFFFFF) {
    printf("false\n");
  }
  else {
    printf("Unknown value: %#010x\n", val);
  }
  return val;
}

/*

Copy over any error-detection functions here

*/


// main should remain unchanged
int main(int argc, char** argv) {
  int result = our_code_starts_here();
  print(result);
  return 0;
}
