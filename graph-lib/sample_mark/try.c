#include <stdio.h>

typedef struct _R1 {
  int m;
} __attribute ((aligned (16))) R1;

typedef struct _R2 {
  int m;
} __attribute ((aligned (4))) R2;

struct R3 {
  R1 a;
  R2 b;
};

struct R3 r;

R1 x[10];

int i;

typedef int more_aligned_int __attribute ((aligned (8)));
typedef more_aligned_int more_aligned_int_array[5];
more_aligned_int j;
more_aligned_int_array k;

int main()
{
  printf ("%d\n", sizeof (struct R3));              /* GCC 32;  CompCert-2.5: 16 */ 
  printf ("%d\n", sizeof (x));                      /* GCC 160; CompCert-2.5: 40 */ 
  printf ("%d\n", __alignof (x));                   /* GCC 16;  CompCert-2.5: 16 */ 
  printf ("%d\n", sizeof (more_aligned_int));       /* GCC 4;   CompCert-2.5: 4  */ 
  printf ("%d\n", sizeof (more_aligned_int_array)); /* GCC 24;  CompCert-2.5: 20 */ 
}

/*
struct T1 {
  int m;
} __attribute ((aligned (16)));

struct T2 {
  int m;
} __attribute ((aligned (4)));

struct T3 {
  struct T1 a;
  struct T2 b;
};

struct T3 p;

struct S1 {
  int m;
};

struct S2 {
  int m;
};

struct S3 {
  struct S1 __attribute ((aligned (16))) a;
  struct S2 __attribute ((aligned (4))) b;
};

struct T3 p;

struct S3 q;
*/
