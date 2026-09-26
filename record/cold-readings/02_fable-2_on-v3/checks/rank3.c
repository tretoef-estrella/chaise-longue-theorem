// Streaming reduced row echelon over GF(3) for sparse rows (CSR). Returns the rank.
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
int rank_gf3(int64_t nrows, int32_t ncols, const int64_t* rowptr, const int32_t* colidx, const uint8_t* val){
    uint8_t* piv = (uint8_t*)calloc((size_t)ncols*(size_t)ncols, 1);
    int32_t* pivlist = (int32_t*)malloc(sizeof(int32_t)*(size_t)ncols);
    uint8_t* v = (uint8_t*)malloc((size_t)ncols);
    int32_t npiv = 0;
    for (int64_t i = 0; i < nrows; i++){
        memset(v, 0, (size_t)ncols);
        for (int64_t p = rowptr[i]; p < rowptr[i+1]; p++){ int32_t c = colidx[p]; v[c] = (uint8_t)((v[c] + val[p]) % 3); }
        for (int32_t t = 0; t < npiv; t++){
            int32_t c = pivlist[t]; uint8_t x = v[c];
            if (!x) continue;
            const uint8_t* pr = piv + (size_t)c*(size_t)ncols;
            if (x == 1){ for (int32_t j = 0; j < ncols; j++){ uint8_t s = (uint8_t)(v[j] + 3 - pr[j]); v[j] = s >= 3 ? s - 3 : s; } }
            else       { for (int32_t j = 0; j < ncols; j++){ uint8_t s = (uint8_t)(v[j] + pr[j]);     v[j] = s >= 3 ? s - 3 : s; } }
        }
        int32_t c0 = -1;
        for (int32_t j = 0; j < ncols; j++) if (v[j]){ c0 = j; break; }
        if (c0 < 0) continue;
        if (v[c0] == 2) for (int32_t j = 0; j < ncols; j++) v[j] = (uint8_t)((v[j]*2) % 3);
        for (int32_t t = 0; t < npiv; t++){
            int32_t c = pivlist[t]; uint8_t* pr = piv + (size_t)c*(size_t)ncols; uint8_t x = pr[c0];
            if (!x) continue;
            if (x == 1){ for (int32_t j = 0; j < ncols; j++){ uint8_t s = (uint8_t)(pr[j] + 3 - v[j]); pr[j] = s >= 3 ? s - 3 : s; } }
            else       { for (int32_t j = 0; j < ncols; j++){ uint8_t s = (uint8_t)(pr[j] + v[j]);     pr[j] = s >= 3 ? s - 3 : s; } }
        }
        memcpy(piv + (size_t)c0*(size_t)ncols, v, (size_t)ncols);
        pivlist[npiv++] = c0;
    }
    free(piv); free(pivlist); free(v);
    return npiv;
}
