#include <immintrin.h>
#include <stdint.h>    // for types uint32_t,uint64_t
#include "portable_endian.h"    // for htole32/64

#include <stdlib.h>
#include <string.h>
#include "blake2.h"
#include "blake2-impl.h"
#include "blake2-config.h"
#include <openssl/rand.h>

#define EBIT 15
#define CLEN 12
#define DIFF 13

#define ROL(x, b)   _mm512_rol_epi64 ((x), (b))
#define SL(x, b)    _mm512_slli_epi64((x), (b))
#define AND(a, b)   _mm512_and_epi64 ((a), (b))
#define XOR(a, b)   _mm512_xor_epi64 ((a), (b))
#define OR(a, b)    _mm512_or_epi64 ((a), (b))
#define ADD(a, b)   _mm512_add_epi64((a), (b))
#define SET(a)      _mm512_set1_epi64((a))
#define STORE       _mm512_store_epi64
#define SET8        _mm512_set_epi64
#define u512        __m512i

#define EN 1 << EBIT
#define CN CLEN << 2
#define M EN << 1
#define MASK (1 << EBIT) - 1

// set siphash keys from 32 byte char array
#define setkeys() \
  k0 = SET(le64toh(((uint64_t *)mesg)[0])); \
  k1 = SET(le64toh(((uint64_t *)mesg)[1])); \
  k2 = SET(le64toh(((uint64_t *)mesg)[2])); \
  k3 = SET(le64toh(((uint64_t *)mesg)[3]));


#define sip_round() \
  v0 = ADD(v0,v1); v2 = ADD(v2,v3); v1 = ROL(v1,13); \
  v3 = ROL(v3,16); v1 = XOR(v1,v0); v3 = XOR(v3,v2); \
  v0 = ROL(v0,32); v2 = ADD(v2, v1); v0 = ADD(v0, v3); \
  v1 = ROL(v1,17); v3 = ROL(v3,21); \
  v1 = XOR(v1,v2); v3 = XOR(v3,v0); v2 = ROL(v2,32); 

#define siphash24() ({\
  v0 = k0; v1 = k1; v2 = k2; v3 = k3; \
  v3 = XOR(v3, nonce); \
  sip_round(); sip_round(); \
  v0 = XOR(v0, nonce); \
  v2 = XOR(v2, k4); \
  sip_round(); sip_round(); sip_round(); sip_round(); \
  h = OR(SL(AND(XOR(XOR(XOR(v0,v1),v2),v3), mask),1),flag); \
  })

/****** random ******/
uint64_t random_u64() {
    union {
        uint64_t i;
        unsigned char c[sizeof(uint64_t)];
    } u;

    if (!RAND_bytes(u.c, sizeof(u.c))) {
        exit(1);
    }

    return u.i;
}
/*** end ****/

/****** blake2b *****/

#ifdef _MSC_VER
#include <intrin.h> /* for _mm_set_epi64x */
#endif
#include <emmintrin.h>
#if defined(HAVE_SSSE3)
#include <tmmintrin.h>
#endif
#if defined(HAVE_SSE41)
#include <smmintrin.h>
#endif
#if defined(HAVE_AVX)
#include <immintrin.h>
#endif
#if defined(HAVE_XOP)
#include <x86intrin.h>
#endif

#include "blake2b-round.h"

static const uint64_t blake2b_IV[8] =
{
  0x6a09e667f3bcc908ULL, 0xbb67ae8584caa73bULL,
  0x3c6ef372fe94f82bULL, 0xa54ff53a5f1d36f1ULL,
  0x510e527fade682d1ULL, 0x9b05688c2b3e6c1fULL,
  0x1f83d9abfb41bd6bULL, 0x5be0cd19137e2179ULL
};

/* Some helper functions */
static void blake2b_set_lastnode( blake2b_state *S )
{
  S->f[1] = (uint64_t)-1;
}

static int blake2b_is_lastblock( const blake2b_state *S )
{
  return S->f[0] != 0;
}

static void blake2b_set_lastblock( blake2b_state *S )
{
  if( S->last_node ) blake2b_set_lastnode( S );

  S->f[0] = (uint64_t)-1;
}

static void blake2b_increment_counter( blake2b_state *S, const uint64_t inc )
{
  S->t[0] += inc;
  S->t[1] += ( S->t[0] < inc );
}

/* init xors IV with input parameter block */
int blake2b_init_param( blake2b_state *S, const blake2b_param *P )
{
  size_t i;
  /*blake2b_init0( S ); */
  const unsigned char * v = ( const unsigned char * )( blake2b_IV );
  const unsigned char * p = ( const unsigned char * )( P );
  unsigned char * h = ( unsigned char * )( S->h );
  /* IV XOR ParamBlock */
  memset( S, 0, sizeof( blake2b_state ) );

  for( i = 0; i < BLAKE2B_OUTBYTES; ++i ) h[i] = v[i] ^ p[i];

  S->outlen = P->digest_length;
  return 0;
}


/* Some sort of default parameter block initialization, for sequential blake2b */
int blake2b_init( blake2b_state *S, size_t outlen )
{
  blake2b_param P[1];

  if ( ( !outlen ) || ( outlen > BLAKE2B_OUTBYTES ) ) return -1;

  P->digest_length = (uint8_t)outlen;
  P->key_length    = 0;
  P->fanout        = 1;
  P->depth         = 1;
  store32( &P->leaf_length, 0 );
  store32( &P->node_offset, 0 );
  store32( &P->xof_length, 0 );
  P->node_depth    = 0;
  P->inner_length  = 0;
  memset( P->reserved, 0, sizeof( P->reserved ) );
  memset( P->salt,     0, sizeof( P->salt ) );
  memset( P->personal, 0, sizeof( P->personal ) );

  return blake2b_init_param( S, P );
}

int blake2b_init_key_with_param( blake2b_state *S, const blake2b_param *P, const void *key, size_t keylen )
{
  if( blake2b_init_param( S, P ) < 0 )
    return 0;

  {
    uint8_t block[BLAKE2B_BLOCKBYTES];
    memset( block, 0, BLAKE2B_BLOCKBYTES );
    memcpy( block, key, keylen );
    blake2b_update( S, block, BLAKE2B_BLOCKBYTES );
    secure_zero_memory( block, BLAKE2B_BLOCKBYTES ); /* Burn the key from stack */
  }
  return 0;
}

int blake2b_init_key( blake2b_state *S, size_t outlen, const void *key, size_t keylen )
{
  blake2b_param P[1];

  if ( ( !outlen ) || ( outlen > BLAKE2B_OUTBYTES ) ) return -1;

  if ( ( !keylen ) || keylen > BLAKE2B_KEYBYTES ) return -1;

  P->digest_length = (uint8_t)outlen;
  P->key_length    = (uint8_t)keylen;
  P->fanout        = 1;
  P->depth         = 1;
  store32( &P->leaf_length, 0 );
  store32( &P->node_offset, 0 );
  store32( &P->xof_length, 0 );
  P->node_depth    = 0;
  P->inner_length  = 0;
  memset( P->reserved, 0, sizeof( P->reserved ) );
  memset( P->salt,     0, sizeof( P->salt ) );
  memset( P->personal, 0, sizeof( P->personal ) );

  if( blake2b_init_param( S, P ) < 0 )
    return 0;

  {
    uint8_t block[BLAKE2B_BLOCKBYTES];
    memset( block, 0, BLAKE2B_BLOCKBYTES );
    memcpy( block, key, keylen );
    blake2b_update( S, block, BLAKE2B_BLOCKBYTES );
    secure_zero_memory( block, BLAKE2B_BLOCKBYTES ); /* Burn the key from stack */
  }
  return 0;
}

static void blake2b_compress( blake2b_state *S, const uint8_t block[BLAKE2B_BLOCKBYTES] )
{
  __m128i row1l, row1h;
  __m128i row2l, row2h;
  __m128i row3l, row3h;
  __m128i row4l, row4h;
  __m128i b0, b1;
  __m128i t0, t1;
#if defined(HAVE_SSSE3) && !defined(HAVE_XOP)
  const __m128i r16 = _mm_setr_epi8( 2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12, 13, 14, 15, 8, 9 );
  const __m128i r24 = _mm_setr_epi8( 3, 4, 5, 6, 7, 0, 1, 2, 11, 12, 13, 14, 15, 8, 9, 10 );
#endif
#if defined(HAVE_SSE41)
  const __m128i m0 = LOADU( block + 00 );
  const __m128i m1 = LOADU( block + 16 );
  const __m128i m2 = LOADU( block + 32 );
  const __m128i m3 = LOADU( block + 48 );
  const __m128i m4 = LOADU( block + 64 );
  const __m128i m5 = LOADU( block + 80 );
  const __m128i m6 = LOADU( block + 96 );
  const __m128i m7 = LOADU( block + 112 );
#else
  const uint64_t  m0 = load64(block +  0 * sizeof(uint64_t));
  const uint64_t  m1 = load64(block +  1 * sizeof(uint64_t));
  const uint64_t  m2 = load64(block +  2 * sizeof(uint64_t));
  const uint64_t  m3 = load64(block +  3 * sizeof(uint64_t));
  const uint64_t  m4 = load64(block +  4 * sizeof(uint64_t));
  const uint64_t  m5 = load64(block +  5 * sizeof(uint64_t));
  const uint64_t  m6 = load64(block +  6 * sizeof(uint64_t));
  const uint64_t  m7 = load64(block +  7 * sizeof(uint64_t));
  const uint64_t  m8 = load64(block +  8 * sizeof(uint64_t));
  const uint64_t  m9 = load64(block +  9 * sizeof(uint64_t));
  const uint64_t m10 = load64(block + 10 * sizeof(uint64_t));
  const uint64_t m11 = load64(block + 11 * sizeof(uint64_t));
  const uint64_t m12 = load64(block + 12 * sizeof(uint64_t));
  const uint64_t m13 = load64(block + 13 * sizeof(uint64_t));
  const uint64_t m14 = load64(block + 14 * sizeof(uint64_t));
  const uint64_t m15 = load64(block + 15 * sizeof(uint64_t));
#endif
  row1l = LOADU( &S->h[0] );
  row1h = LOADU( &S->h[2] );
  row2l = LOADU( &S->h[4] );
  row2h = LOADU( &S->h[6] );
  row3l = LOADU( &blake2b_IV[0] );
  row3h = LOADU( &blake2b_IV[2] );
  row4l = _mm_xor_si128( LOADU( &blake2b_IV[4] ), LOADU( &S->t[0] ) );
  row4h = _mm_xor_si128( LOADU( &blake2b_IV[6] ), LOADU( &S->f[0] ) );
  ROUND( 0 );
  ROUND( 1 );
  ROUND( 2 );
  ROUND( 3 );
  ROUND( 4 );
  ROUND( 5 );
  ROUND( 6 );
  ROUND( 7 );
  ROUND( 8 );
  ROUND( 9 );
  ROUND( 10 );
  ROUND( 11 );
  row1l = _mm_xor_si128( row3l, row1l );
  row1h = _mm_xor_si128( row3h, row1h );
  STOREU( &S->h[0], _mm_xor_si128( LOADU( &S->h[0] ), row1l ) );
  STOREU( &S->h[2], _mm_xor_si128( LOADU( &S->h[2] ), row1h ) );
  row2l = _mm_xor_si128( row4l, row2l );
  row2h = _mm_xor_si128( row4h, row2h );
  STOREU( &S->h[4], _mm_xor_si128( LOADU( &S->h[4] ), row2l ) );
  STOREU( &S->h[6], _mm_xor_si128( LOADU( &S->h[6] ), row2h ) );
}


int blake2b_update( blake2b_state *S, const void *pin, size_t inlen )
{
  const unsigned char * in = (const unsigned char *)pin;
  if( inlen > 0 )
  {
    size_t left = S->buflen;
    size_t fill = BLAKE2B_BLOCKBYTES - left;
    if( inlen > fill )
    {
      S->buflen = 0;
      memcpy( S->buf + left, in, fill ); /* Fill buffer */
      blake2b_increment_counter( S, BLAKE2B_BLOCKBYTES );
      blake2b_compress( S, S->buf ); /* Compress */
      in += fill; inlen -= fill;
      while(inlen > BLAKE2B_BLOCKBYTES) {
        blake2b_increment_counter(S, BLAKE2B_BLOCKBYTES);
        blake2b_compress( S, in );
        in += BLAKE2B_BLOCKBYTES;
        inlen -= BLAKE2B_BLOCKBYTES;
      }
    }
    memcpy( S->buf + S->buflen, in, inlen );
    S->buflen += inlen;
  }
  return 0;
}


int blake2b_final( blake2b_state *S, void *out, size_t outlen )
{
  if( out == NULL || outlen < S->outlen )
    return -1;

  if( blake2b_is_lastblock( S ) )
    return -1;

  blake2b_increment_counter( S, S->buflen );
  blake2b_set_lastblock( S );
  memset( S->buf + S->buflen, 0, BLAKE2B_BLOCKBYTES - S->buflen ); /* Padding */
  blake2b_compress( S, S->buf );

  memcpy( out, &S->h[0], S->outlen );
  return 0;
}


int blake2b( void *out, size_t outlen, const void *in, size_t inlen, const void *key, size_t keylen )
{
  blake2b_state S[1];

  /* Verify parameters */
  if ( NULL == in && inlen > 0 ) return -1;

  if ( NULL == out ) return -1;

  if( NULL == key && keylen > 0 ) return -1;

  if( !outlen || outlen > BLAKE2B_OUTBYTES ) return -1;

  if( keylen > BLAKE2B_KEYBYTES ) return -1;

  if( keylen )
  {
    if( blake2b_init_key( S, outlen, key, keylen ) < 0 ) return -1;
  }
  else
  {
    if( blake2b_init( S, outlen ) < 0 ) return -1;
  }

  blake2b_update( S, ( const uint8_t * )in, inlen );
  blake2b_final( S, out, outlen );
  return 0;
}

int blake2( void *out, size_t outlen, const void *in, size_t inlen, const void *key, size_t keylen ) {
  return blake2b(out, outlen, in, inlen, key, keylen);
}

#if defined(SUPERCOP)
int crypto_hash( unsigned char *out, unsigned char *in, unsigned long long inlen )
{
  return blake2b( out, BLAKE2B_OUTBYTES, in, inlen, NULL, 0 );
}
#endif

void b2setup(blake2b_state *S) {
    int i;

    blake2b_param P;

    P.digest_length = 32;
    P.key_length = 0;
    P.fanout = 1;
    P.depth = 1;
    P.leaf_length = 0;
    P.xof_length = 0;
    P.node_offset = 0;
    P.inner_length = 0;
    P.node_depth = 0;
    
    for(i=0; i<14; ++i) {
        P.reserved[i] = 0;
    }

    for(i=0; i<BLAKE2B_SALTBYTES; ++i) {
        P.salt[i] = 0;
    }

    uint8_t personal[] = {99, 107, 98, 45, 100, 101, 102, 97, 117, 108, 116, 45, 104, 97, 115, 104};

    for(i=0; i<16; ++i) {
        P.personal[i] = personal[i];
    }

    blake2b_init_param(S, &P);
}

/**** end ******/


/***** SOVE *****/
int c_solve(uint32_t *prof, uint64_t *nonc, const uint8_t *hash) {
  int graph[M];
  uint64_t *G = _mm_malloc(sizeof(uint64_t) * M, 64);
  int path[CLEN];

  uint8_t pmesg[40];
  uint8_t hmesg[CN];
  uint8_t mesg[32];

  blake2b_state S;

  u512 k0, k1, k2, k3, k4;
  u512 v0, v1, v2, v3, nonce, mask, flag;
  u512 h;
  uint64_t e3,e2,e1,e0;
  
  k4 = SET(0xff);
  mask = SET(MASK);
  flag = SET8(1,0,1,0,1,0,1,0);

  b2setup(&S);
  
  memcpy(pmesg+8, hash, 32);
  
  for(int gs=1; gs<200; ++gs) {
    RAND_bytes(pmesg, 8);
((uint64_t *)pmesg)[0] = gs;    
    blake2b_state tmp = S;
    blake2b_update(&tmp, pmesg, 40);
    blake2b_final(&tmp, mesg, 32);

    setkeys();
    
    #pragma ivdep
    for(uint64_t i=0, j=0; i<EN;) {
        e0 = i; ++i; e1 = i; ++i;
        e2 = i; ++i; e3 = i; ++i;
        nonce = OR(SL(SET8(e3,e3,e2,e2,e1,e1,e0,e0), 1),flag);
        siphash24();
        STORE(G+j, h);
        graph[j] = -1; ++j; graph[j] = -1; ++j;
        graph[j] = -1; ++j; graph[j] = -1; ++j;
        graph[j] = -1; ++j; graph[j] = -1; ++j;
        graph[j] = -1; ++j; graph[j] = -1; ++j;
    }

    for(uint64_t i=0; i<M;) {
        uint64_t u = G[i]; ++i;
        uint64_t v = G[i]; ++i;

        int pre = -1;
        int cur = u;
        int next;
        while(cur != -1) {
            next = graph[cur];
            graph[cur] = pre;
            pre = cur;
            cur = next;
        }

        int m = 0;
        cur = v;
        while(graph[cur] != -1 && m < CLEN) {
            cur = graph[cur];
            ++m;
        }

        if(cur != u) {
            graph[u] = v;
        } else if(m == CLEN-1) {
                int j;  
                cur = v;
                for(j=0; j<=m; ++j) {
                    path[j] = cur;
                    cur = graph[cur];
                }

                for(j=0; j<M; ++j) {
                    graph[j] = -1;
                }
                
                for(j=1; j<=m; ++j) {
                    graph[path[j]] = path[j-1];
                }

                int k = 0;
                int b = CLEN -1;
                for(j=0; k < b; ) {
                    uint64_t u = G[j]; ++j;
                    uint64_t v = G[j]; ++j;

                    if(graph[u] == v || graph[v] == u) {
                        prof[k] = (j >> 1) - 1;
                        ++k;
                    }
                }

                prof[k] = (i >> 1) -1;
                
                memcpy(hmesg, prof, CN);
                blake2b_state tmp = S;
                blake2b_update(&tmp, hmesg, CN);
                blake2b_final(&tmp, mesg, 32);
                
                if(mesg[0] == 0 && mesg[1] == 0) {
                    prof[CLEN] = 1;
                    *nonc = le64toh(((uint64_t *)pmesg)[0]);
                    _mm_free(G);
                    return gs;
                }
        }

    }
  }
  _mm_free(G);
  prof[CLEN] = 0;
  return 200;
}


#include "time.h"
#include <stdio.h>

int main() {
  // uint64_t *G = _mm_malloc(sizeof(uint64_t) * M, 64);
    uint32_t proof[20];
    uint8_t msg[40];
    uint64_t nonc;
    clock_t start, finish;
    double  duration;
    int k = 0;
    int n = 1000;
    start = clock();

    for(int i=0; i<40; ++i)
    msg[i] = 0;

    for(int i=0; i<n; ++i) {
        msg[0] = i;
        c_solve(proof, &nonc, msg);
        if (proof[CLEN] == 1) {
            ++k;
            // printf("%lu %d %d %d %d %d %d\n",nonc, proof[0], proof[1], proof[2], proof[3], proof[4], proof[5]);
            // for(int i=0; i<CLEN; ++i) {
            //   printf("%d, ", proof[i]);
            // }
            // printf("\n");
        }
    }
    finish = clock();
    duration = (double)(finish - start) / (CLOCKS_PER_SEC/1000.0) / n;
    uint64_t a[2];
    printf("%lu %d %f ms\n", nonc, k, duration);
    
    // uint8_t test[8];
    // RAND_bytes(test, 8);
    // uint64_t nonc = htole64(((uint64_t *)test)[0]);
    // uint64_t nonc2 = le64toh(((uint64_t *)test)[0]);
    // // *test = le64toh(nonc);

    // printf("%lu %lu\n", nonc, nonc2);

    return 0;
}