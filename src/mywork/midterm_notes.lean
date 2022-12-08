--iff notes
variables (P Q: Prop)
-- variables (pq: P → Q) (qp: Q → P)

-- example : P ↔ Q := (iff.intro pq qp)
variable piffq: P ↔ Q
example : P → Q := iff.mp piffq
example : Q → P := iff.mpr piffq   

theorem my_and_elim : ∀ (P Q), P ∧ Q → P :=
begin 
assume P Q,
assume (pq : P ∧ Q),
apply and.elim_left pq,
end  

-- English example:
-- variables (Smoke Fire Light Good : Prop)
-- variables (sf : Smoke → Fire) (fl: Fire → Light) (lg: Light → Good)
-- variables (s: Smoke) --apply sf to s to get a proof of fire, then so on

example : ∀ (S F L G : Prop), (S → F) → (F → L) → (L → G) → (S → G):= 
begin 
  assume S F L G,
  assume sf fl lg,
  assume s,
  -- apply lg,
  -- apply fl,
  -- apply sf,
  -- exact s,
  exact (lg (fl ( sf s))),
end

--Negation example
example : ∀ (P: Prop), ¬(P ∧ ¬P) := --need to prove the contradiction to show that the not is true
begin
  assume P,
  assume pandnp,
  cases pandnp with p np,
  apply false.elim (np p), --apply a proof of np to p gives false, which shows why the false-elim works
  --since it is show that is false, the proof is satisfied through contradiction
end