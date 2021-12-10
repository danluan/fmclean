intro h,
split,
apply le_of_succ_le_succ,
have h2 := le_succ (succ a) b h,
exact h2,

intro h2,
have h3 := le_trans (succ a) b a h h2,
have hboom := not_succ_le_self a h3,
exact hboom,
--ALELUIA