induction n with k hk,
rw pow_zero (a ^ m),
rw mul_zero m,
rw pow_zero a,
refl,
rw pow_succ (a ^ m) k,
rw hk,
rw mul_succ m k,
rw pow_add a (m * k) m,
refl,