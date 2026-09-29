import RequestProject.Monotone.Main
import RequestProject.Monotone.Checks
open ChainLemma
#check @Partition.size
#check @ChainLemma.opt_weakDom_opt
#check @ChainLemma.card_opt_mem_le
#check @ChainLemma.opt_count_gt_isDownSet_within
#check @ChainLemma.parity_hypothesis_needed
#print axioms ChainLemma.opt_weakDom_opt
#print axioms ChainLemma.card_opt_mem_le
#print axioms ChainLemma.opt_count_gt_isDownSet_within
#print axioms ChainLemma.parity_hypothesis_needed
