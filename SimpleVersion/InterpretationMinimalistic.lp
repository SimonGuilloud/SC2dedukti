require open lisa2dedukti.SimpleVersion.FOL;
require open lisa2dedukti.SimpleVersion.prelude;
require open lisa2dedukti.SimpleVersion.SequentCalculus;

//Here we do layered interpretation in minimal logic

//First we interpret sequents with exactly one formula on the right into functions over formulas

injective symbol fprf : Formula → TYPE;

rule prf (seq Nil ($x ⸬ Nil)) ↪ fprf ($x);
rule prf (seq ($y ⸬ $l)  ($x ⸬ Nil)) ↪ (fprf $y) → prf (seq $l  ($x ⸬ Nil));

//Then we interpret Formulas of minimal logic over TYPES.

rule fprf (Implies $ϕ $ψ) ↪ fprf $ϕ → fprf $ψ;
rule fprf (Forall $P) ↪ Π x : Term, fprf ($P x);


//Minimalistic rules
//We translate structural rules, Cut and Implies and Forall rules in the case of minimal logic, i.e. when the right handside of a sequent contains exactly one formula.
//Minimalistic logic also uses ⊥, but has no dedicated axiom for it: It behaves like a free symbol.

//symbol Hypothesis ϕ Γ Δ : prf (seq (ϕ ⸬ Γ) (ϕ ⸬ Δ));
rule Hypothesis $ϕ Nil Nil ↪ λ x, x; //In the minimalistic case, Δ = Nil
rule Hypothesis $ϕ ($x ⸬ $Γ) Nil ↪ λ x y, Hypothesis $ϕ $Γ Nil x;

//symbol Swap2Left Γ Δ (n : Nat) : prf (seq Γ Δ) → prf (seq (swap2 Γ n) Δ);
rule Swap2Left Nil _ _ ↪ λ x, x;
rule Swap2Left ($x ⸬ Nil) _ _ ↪ λ x, x;
rule Swap2Left ($x ⸬ $y ⸬ $l) (_ ⸬ Nil) 0 ↪ λ p x y, p y x;
rule Swap2Left ($x ⸬ $y ⸬ $l) ($f ⸬ Nil) (S $n) ↪ λ p x, Swap2Left ($y ⸬ $l) ($f ⸬ Nil) $n (p x) ;
//symbol Swap2Right Γ Δ (n : Nat) : prf (seq Γ Δ) → prf (seq Γ (swap2 Δ n));
//In minimalistic logic, Swap2Right can only be trivial
rule Swap2Right _ (_ ⸬ Nil) _ ↪ λ x, x;


//symbol ContractLeft x Γ Δ : prf (seq (x ⸬ x ⸬ Γ) Δ) → prf (seq (x ⸬ Γ) Δ);
rule ContractLeft _ _ (_ ⸬ Nil) ↪ λ p px, p px px;
//symbol ContractRight x Γ Δ : prf (seq Γ (x ⸬ x ⸬ Δ) ) → prf (seq Γ (x ⸬ Δ));
//Can't be applied in minimal or intuitionistic logic.


//symbol LeftWeakening Σ Γ Δ : prf (seq Γ Δ) → prf (seq (append Σ Γ) Δ);
rule LeftWeakening Nil $Γ ($f ⸬ Nil) ↪ λ x, x;
rule LeftWeakening ($x ⸬ $Σ) $Γ ($f ⸬ Nil) ↪ λ p x, LeftWeakening $Σ $Γ ($f ⸬ Nil) p;
//symbol RightWeakening Γ Ω Δ : prf (seq Γ Δ) → prf (seq Γ (append Ω Δ));
//Can't be applied in minimal logic


//symbol Cut Γ Σ Δ Ω ϕ : prf (seq Γ (ϕ ⸬ Δ)) → prf (seq (ϕ ⸬ Σ) Ω) → prf (seq (append Γ Σ) (append Δ Ω));
rule Cut Nil $Σ Nil (_ ⸬ Nil) _ ↪ λ π1 π2, π2 π1; //In minimalistic logic, Δ = Nil and Ω = (_ ⸬ Nil)
rule Cut (_ ⸬ $Γ) $Σ Nil ($f ⸬ Nil) $ϕ ↪ λ π1 π2 x, Cut $Γ $Σ Nil ($f ⸬ Nil) $ϕ (π1 x) π2;

//symbol RightImplies Γ ϕ ψ Δ : prf (seq (ϕ ⸬ Γ) (ψ ⸬ Δ)) → prf (seq Γ ((Implies ϕ ψ) ⸬ Δ));
rule RightImplies Nil $ϕ $ψ Nil ↪ λ p1 p2, p1 p2;
rule RightImplies (_ ⸬ $l) $ϕ $ψ Nil ↪ λ π x, (RightImplies $l $ϕ $ψ Nil) λ q, π q x ;
//symbol LeftImplies Γ Σ Δ Ω ϕ ψ :  prf (seq Γ (ϕ ⸬ Δ)) → prf (seq (ψ ⸬ Σ) Ω) → prf (seq ((Implies ϕ ψ) ⸬ (append Γ Σ)) (append Δ Ω));
rule LeftImplies Nil _ Nil ($f ⸬ Nil) $ϕ $ψ ↪ λ phi psif phipsi, psif (phipsi phi);
rule LeftImplies ($x ⸬ $Γ) $Σ Nil ($f ⸬ Nil) $ϕ $ψ ↪ λ xpphi psipf phipsi x, LeftImplies $Γ $Σ Nil ($f ⸬ Nil) $ϕ $ψ (xpphi x) psipf phipsi;


//symbol RightForall Γ ϕ Δ : (Π x:Term, prf (seq Γ ((ϕ x) ⸬ Δ))) → prf (seq Γ ((Forall ϕ) ⸬ Δ));
rule RightForall Nil $ϕ Nil ↪ λ px, px;
rule RightForall ($x ⸬ $Γ) $ϕ Nil ↪ λ p px, RightForall $Γ $ϕ Nil (λ x1, p x1 px);
//symbol LeftForall Γ ϕ t Δ : prf (seq ((ϕ t) ⸬ Γ) Δ) → prf (seq ((Forall ϕ) ⸬ Γ) Δ);
rule LeftForall $Γ $ϕ $t ($f ⸬ Nil) ↪ λ px ax, px (ax $t);
