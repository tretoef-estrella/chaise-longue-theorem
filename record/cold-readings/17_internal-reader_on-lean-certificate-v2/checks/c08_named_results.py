# c08: for each row of the certificate §3 table, print the statement (source text up to ':=') of every
# "Main Lean result" it names, from the folder of that piece, so that each can be read against v12.
import os, re, glob
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RP = os.path.join(ROOT, 'material', 'project', 'RequestProject')
ROWS = [('E1','BipAny',['thm76_any','theoremC_any','choose_pred_prime_pow','thm76_prime_pow','theoremC_prime_pow']),
 ('E2','EvenCount',['QkEven_eq','card_closedPointed','card_Gamma_even','finrank_IK_le_even']),
 ('E3','Odd3',['O_ge_three','I_odd_one_eq_DIdeal','card_Z_le_finrank']),
 ('E4','Pow2',['prop92_ge','quartic_char_two','pow2_of_oddbox','lowest_forms']),
 ('E5','EvenAssembly',['HypH','theorem_i','theorem_ii','theorem_iii',"mainTheorem'_four"]),
 ('E6','OddShapes',['A0','A1','A2','A3','A4','optS_filter_eq_Icc','isInterlaced_root_even','isInterlaced_root_odd']),
 ('E7','OddLayers',['isInterlaced_layerS','card_ZS_root_even','card_ZS_root_odd']),
 ('E8','Pfaffian',['pf_eq_sum_matchings','bpf_laplace','bpf_expand_var','C1','C2','C3','C4','C5','C6']),
 ('E9','RankTwo',['R4',"R4'",'S2','S5a','S5b']),
 ('E10','Membership',['M2a','M2b','M3_pos','M3_zero','V1']),
 ('E11','OddPatterns',['mPf','VS','VSAll','C3','D3']),
 ('E12','OddLifts',['P1','P2','P3','T1','T2','T3','T4','T5']),
 ('E13','OddLifts2',['Q1','Q2',"Q'1","Q'2",'T6','T7','T8']),
 ('E14','OddTheorem',['lemmaK','prop810','theorem811','theoremO']),
 ('E16','EvenBlocks',['lemma94','exists_setting','SInv','lemma95']),
 ('E17','EvenColours',['C2','C4_even','C4_odd']),
 ('E18','EvenMinus',['lemma97','lemma98','lemma99','lemmaM5','lemmaM6']),
 ('E19','EvenOne',['lemma910','E1','E2','E3']),
 ('E20','EvenAll',['A3','B1','B2',"mainTheorem'",'D2','E1','E2']),
 ('E15','OddEquality',['D1','D2_DJ','D2_M','A5','B3','partC'])]
for e, fo, names in ROWS:
    print('=' * 100); print(e, fo)
    srcs = {f: open(f, encoding='utf-8').read() for f in sorted(glob.glob(os.path.join(RP, fo, '*.lean')))}
    for n in names:
        found = False
        for f, s in srcs.items():
            m = re.search(r'^(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure)\s+' + re.escape(n) + r'(?=[\s({\[:])(.*?)(:=|\bwhere\b)', s, re.S | re.M)
            if m:
                found = True
                stmt = re.sub(r'\s+', ' ', m.group(2)).strip()
                print(f'  [{os.path.basename(f)}] {m.group(1)} {n}{" " if stmt else ""}{stmt[:700]}')
                break
        if not found: print(f'  !! {n} NOT FOUND as a declaration in {fo}/')
