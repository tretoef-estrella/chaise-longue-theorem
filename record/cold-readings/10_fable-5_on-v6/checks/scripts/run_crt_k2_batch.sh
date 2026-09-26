#!/bin/zsh
# sequential batch of the k=2 colouring (CRT) runs under the watchdog; one run at a time
cd /Users/rafa/Desktop/LECTORES_EN_FRIO/FABLE_5/checks
./scripts/capped_run.sh logs/crt_k2_m15_p3_symfull_audit40.log "Σ_c dim = Q_2(15) = 32900 (paper §12.3: 1001 colourings with non-zero image at p=3); est < 5 min, < 300 MB" python3 scripts/crt_colouring_k2.py 15 3 --k 2 --sym full --audit 40
./scripts/capped_run.sh logs/crt_k2_m15_p5_symgalois_audit20.log "Σ_c dim = Q_2(15) = 32900 (paper: 141 colourings with non-zero image at p=5); est < 10 min, < 500 MB" python3 scripts/crt_colouring_k2.py 15 5 --k 2 --sym galois --audit 20
./scripts/capped_run.sh logs/crt_k2_m21_p7_symfull_audit10.log "Σ_c dim = Q_2(21) = 102800 (paper: 141 colourings with non-zero image at p=7); est < 10 min, < 700 MB" python3 scripts/crt_colouring_k2.py 21 7 --k 2 --sym full --audit 10
./scripts/capped_run.sh logs/crt_k2_m21_p3_symfull_audit40.log "Σ_c dim = Q_2(21) = 102800 (paper: 3301 colourings with non-zero image at p=3); est < 10 min, < 300 MB" python3 scripts/crt_colouring_k2.py 21 3 --k 2 --sym full --audit 40
./scripts/capped_run.sh logs/crt_k2_m9_p3_control.log "CONTROL prime power m=9 (r=1, one colouring = the whole ring 9^5): dim = Q_2(9) = 5120; est < 10 min, < 900 MB" python3 scripts/crt_colouring_k2.py 9 3 --k 2 --sym none
echo BATCH_DONE
