#include <stdio.h>
#include <string.h>
#include <stdint.h>  

int main() {
  uint32_t a[] = {1,2,3,4};
  uint8_t  b[16];

  memcpy(b, a, 16);

  for(int i=0; i<16; ++i) {
    printf("%d ", b[i]);
  }
  printf("\n");
}