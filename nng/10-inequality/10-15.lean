intro h,
cases h with p1 p2,
cases p1 with n p3, 
induction n with m hm,

rw add_zero at p3,
exfalso,
apply p2,
use 0, rw add_zero,
symmetry,
exact p3,

rw le_iff_exists_add, use m,
rw succ_add,
rw add_succ at p3,
exact p3,