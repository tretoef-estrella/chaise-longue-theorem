// Streaming RREF over GF(p), p < 16, sparse CSR rows. Returns the rank.
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
int rank_gfp(int64_t nrows, int32_t ncols, const int64_t* rowptr, const int32_t* colidx, const uint8_t* val, int p){
    uint8_t* piv = (uint8_t*)calloc((size_t)ncols*(size_t)ncols, 1);
    int32_t* pivlist = (int32_t*)malloc(sizeof(int32_t)*(size_t)ncols);
    uint8_t* v = (uint8_t*)malloc((size_t)ncols);
    uint8_t inv[16]; for (int a=1;a<p;a++) for (int b=1;b<p;b++) if ((a*b)%p==1) inv[a]=(uint8_t)b;
    int32_t npiv = 0;
    for (int64_t i = 0; i < nrows; i++){
        memset(v, 0, (size_t)ncols);
        for (int64_t q = rowptr[i]; q < rowptr[i+1]; q++){ int32_t c = colidx[q]; v[c] = (uint8_t)((v[c] + val[q]) % p); }
        for (int32_t t = 0; t < npiv; t++){
            int32_t c = pivlist[t]; uint8_t x = v[c];
            if (!x) continue;
            const uint8_t* pr = piv + (size_t)c*(size_t)ncols; int m = p - x;   // v += m*pr
            for (int32_t j = 0; j < ncols; j++){ v[j] = (uint8_t)((v[j] + m*pr[j]) % p); }
        }
        int32_t c0 = -1;
        for (int32_t j = 0; j < ncols; j++) if (v[j]){ c0 = j; break; }
        if (c0 < 0) continue;
        int s = inv[v[c0]];
        for (int32_t j = 0; j < ncols; j++) v[j] = (uint8_t)((v[j]*s) % p);
        for (int32_t t = 0; t < npiv; t++){
            int32_t c = pivlist[t]; uint8_t* pr = piv + (size_t)c*(size_t)ncols; uint8_t x = pr[c0];
            if (!x) continue; int m = p - x;
            for (int32_t j = 0; j < ncols; j++){ pr[j] = (uint8_t)((pr[j] + m*v[j]) % p); }
        }
        memcpy(piv + (size_t)c0*(size_t)ncols, v, (size_t)ncols);
        pivlist[npiv++] = c0;
    }
    free(piv); free(pivlist); free(v);
    return npiv;
}
