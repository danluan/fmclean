intro pq,
intro qr,
intro p,
have q : Q := pq p,
have r : R := qr q,
exact r,