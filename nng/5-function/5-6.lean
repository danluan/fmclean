intro hpqr,
intro hpq,
intro hp,
have hq : Q := hpq hp,
have hr : R := hpqr hp hq,
exact hr,