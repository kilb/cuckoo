#include <stdint.h>    // for types uint32_t,uint64_t
#include "portable_endian.h"    // for htole32/64

#define rotl(x, b) ((x) << (b)) | ((x) >> (64 - (b)))
#define EBIT 10
#define CLEN 8

#define EN 1 << EBIT
#define M EN << 1
#define MASK (1 << EBIT) - 1

int graph[M];
int graph2[M];
int V[EN], U[EN];
int P1[EN], P2[EN];
// int degree[M];

uint64_t k0, k1, k2, k3;
uint64_t v0, v1, v2, v3;
// set siphash keys from 32 byte char array
void setkeys(const uint8_t *keybuf) {
  k0 = htole64(((uint64_t *)keybuf)[0]);
  k1 = htole64(((uint64_t *)keybuf)[1]);
  k2 = htole64(((uint64_t *)keybuf)[2]);
  k3 = htole64(((uint64_t *)keybuf)[3]);
}

inline void sip_round() {
  v0 += v1; v2 += v3; v1 = rotl(v1,13);
  v3 = rotl(v3,16); v1 ^= v0; v3 ^= v2;
  v0 = rotl(v0,32); v2 += v1; v0 += v3;
  v1 = rotl(v1,17); v3 = rotl(v3,21);
  v1 ^= v2; v3 ^= v0; v2 = rotl(v2,32);
}

inline uint64_t siphash24(const uint64_t nonce) {
  v0 = k0; v1 = k1; v2 = k2; v3 = k3;
  v3 ^= nonce;
  sip_round(); sip_round();
  v0 ^= nonce;
  v2 ^= 0xff;
  sip_round(); sip_round(); sip_round(); sip_round();

  return (v0 ^ v1) ^ (v2  ^ v3);
}


inline int path(int b, int *P) {
    int i = 0;
    while(graph[b] != -1) {
        *(P+i) = b;
        b = graph[b];
        ++i;
    }
    *(P+i) = b;
    return i; 
}


int c_solve(uint32_t *prof, const uint8_t *mesg) {
  setkeys(mesg);
 
  for(int i=0; i<M; ++i) {
      graph[i] = -1;
      graph2[i] = -1;
  }
  
  for(uint64_t i=0; i<EN; ++i) {
      int u = (siphash24(i<<1) & MASK) << 1;
      int v = ((siphash24((i<<1)+1) & MASK) << 1) + 1;
      
      U[i] = u;
      V[i] = v;

      int ui = path(u, P1);
      int vi = path(v, P2);

      if(P1[ui] == P2[vi]) {
          --ui;
          --vi;
          while(P1[ui] == P2[vi]) {
              --ui;
              --vi;
          }

          if((ui+vi+2+1) == CLEN) {
              int j;
              for(j=0; j<=ui; ++j) {
                  graph2[P1[j]] = P1[j+1];
              }
             if(vi == -1) {
                 graph2[P1[j]] = P1[0];
             } else {
                graph2[P1[j]] = P2[vi];

                for(j=vi; j>0; --j) {
                    graph2[P2[j]] = P2[j-1];
                }
                graph2[P2[j]] = P1[0];
             }
              int k = 0;
              int b = CLEN -1;
              for(j=0; k < b; ++j) {
                  int u = U[j];
                  int v = V[j];

                  if(graph2[u] == v) {
                      prof[k] = j;
                      ++k;
                  } else if(graph2[v] == u) {
                      prof[k] = j;
                      ++k;
                  }
              }
              prof[k] = i;
              return 1;
          }

      } else if(ui < vi) {
          while(ui > 0) {
              graph[P1[ui]] = P1[ui-1];
              --ui;
          }
          graph[u] = v;
      } else {
          while(vi > 0) {
              graph[P2[vi]] = P2[vi-1];
              --vi;
          }
          graph[v] = u;
      }

  }

  return 0;
}
