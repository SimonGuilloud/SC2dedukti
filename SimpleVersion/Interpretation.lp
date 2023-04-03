require open lisa2dedukti.SimpleVersion.FOL;
require open lisa2dedukti.SimpleVersion.prelude;
require open lisa2dedukti.SimpleVersion.SequentCalculus;


rule $x ∧ $y ↪ Neg (Implies $x (Neg $y));

rule $x ∨ $y ↪ Implies (Neg $x)  $y;

rule (Iff $x $y) ↪ (Implies $x $y) ∧ (Implies $y $x);

rule Exists $f ↪ Neg (Forall λ x, (Neg ($f x)));

rule ExistsOne $f ↪ Exists (λ y, (Forall (λ x, Iff (Equality x y) ($f x))));


//Reformulating LK rules in term of Hypothesis, LeftForall, RightForall, LeftImplies, RightImplies

type LeftAnd;
compute Π Γ: List formula, Π ϕ: Formula, Π ψ: Formula, Π Δ: List formula, prf (seq (ϕ ⸬ (ψ ⸬ Γ)) Δ) → prf (seq ((ϕ ∧ ψ) ⸬ Γ) Δ);




//This is a theorem that always holds. Translation needs to reduce it.
rule (swap-multi (enumerate 2 $Γ) $Γ ($ψ ⸬ ($ϕ ⸬ Nil))) ↪ ($ψ ⸬ ($ϕ ⸬ $Γ));

symbol test ϕ ψ Γ Δ ≔ SwapLeft (ϕ ⸬ ψ ⸬ Γ) Δ (1 ⸬ 0 ⸬ (enumerate 2 Γ));
type test;
symbol testT ϕ ψ Γ Δ ≔ prf (seq (swap-multi (1 ⸬ (0 ⸬ enumerate 2 Γ)) (ϕ ⸬ (ψ ⸬ Γ)) Nil) Δ);
compute testT;

symbol SwapHeadLeft ϕ ψ Γ Δ : prf( seq (ϕ ⸬ ψ ⸬ Γ) Δ) → prf( seq (ψ ⸬ ϕ ⸬ Γ) Δ) ≔ SwapLeft (ϕ ⸬ ψ ⸬ Γ) Δ (1 ⸬ 0 ⸬ (enumerate 2 Γ));

rule LeftAnd $Γ $ϕ $ψ $Δ ↪ λ p: prf (seq ($ϕ ⸬ $ψ ⸬ $Γ) $Δ), 
                           (LeftNot $Γ (Implies $ϕ (Neg $ψ)) $Δ 
                                                              (RightImplies $Γ $ϕ (Neg $ψ) $Δ 
                                                                                            (RightNot ($ϕ ⸬ $Γ) $ψ $Δ 
                                                                                                                    (SwapHeadLeft $ϕ $ψ $Γ $Δ p)))) ;
symbol LeftOrBis Γ Σ Δ Ω ϕ ψ : prf (seq (ϕ ⸬ Γ) Δ) → prf (seq  (ψ ⸬ Σ) Ω) → prf (seq ((ϕ ∨ ψ) ⸬ (append Γ Σ)) (append Δ Ω)) ≔
  begin
    assume Γ Σ Δ Ω ϕ ψ p1 p2;
    refine LeftImplies Γ Σ Δ Ω (Neg ϕ) ψ _ _
      { refine RightNot Γ ϕ Δ p1; } 
      { apply p2; }
  end;


symbol LeftOrTer Γ Σ Δ Ω ϕ ψ : prf (seq (ϕ ⸬ Γ) Δ) → prf (seq  (ψ ⸬ Σ) Ω) → prf (seq ((ϕ ∨ ψ) ⸬ (append Γ Σ)) (append Δ Ω)) ≔
  begin
    assume Γ Σ Δ Ω ϕ ψ p1 p2 ;
    refine LeftImplies Γ Σ Δ Ω (Neg ϕ) ψ (RightNot Γ ϕ Δ p1) p2;
  end;


rule LeftOr $Γ $Σ $Δ $Ω $ϕ $ψ ↪ λ (p1 : prf (seq ($ϕ ⸬ $Γ) $Δ)),  λ (p2 : prf (seq  ($ψ ⸬ $Σ) $Ω)),
     (LeftImplies $Γ $Σ $Δ $Ω (Neg $ϕ) $ψ
          (RightNot $Γ $ϕ $Δ p1)
          p2
);

symbol RightAndProof Γ Σ Δ Ω ϕ ψ : prf (seq Γ (ϕ ⸬ Δ)) → prf (seq  Σ (ψ ⸬ Ω)) → prf (seq (append Γ Σ) ((ϕ ∧ ψ) ⸬ (append Δ Ω))) ≔
  begin
    assume Γ Σ Δ Ω ϕ ψ p1 p2;
    refine RightNot (append Γ Σ) (Implies ϕ (Neg ψ)) (append Δ Ω) _;
    refine LeftImplies Γ Σ Δ Ω ϕ (Neg ψ) p1 _; 
    refine LeftNot Σ ψ Ω p2;
  end;

compute RightAndProof ;

rule RightAnd ↪ RightAndProof;


symbol RightOrProof Γ ϕ ψ Δ : prf (seq Γ (ϕ ⸬ ψ ⸬ Δ)) → prf (seq Γ ((ϕ ∨ ψ) ⸬ Δ)) ≔
  begin
    assume Γ ϕ ψ Δ p1;
    refine RightImplies Γ (Neg ϕ) ψ Δ _;
    refine LeftNot Γ ϕ (ψ ⸬ Δ) p1;
  end;
rule RightOr ↪ RightOrProof;

symbol LeftIffProof Γ ϕ ψ Δ ≔ LeftAnd Γ (Implies ϕ ψ) (Implies ψ ϕ) Δ;
rule LeftIff ↪ LeftIffProof;

symbol RightIffProof Γ Σ Δ Ω ϕ ψ  ≔ RightAnd Γ Σ Δ Ω (Implies ϕ ψ) (Implies ψ ϕ) ;
rule RightIff ↪ RightIffProof;

symbol LeftExistsProof Γ ϕ Δ : (Π x:Term, prf (seq ((ϕ x) ⸬ Γ) Δ)) → prf (seq ((Exists ϕ) ⸬ Γ) Δ) ≔
  begin
    assume Γ ϕ Δ family;
    refine LeftNot Γ (Forall (λ x, (Neg (ϕ x)))) Δ _;
    refine RightForall Γ (λ x, (Neg (ϕ x))) Δ _;
    assume x;
    refine RightNot Γ (ϕ x) Δ (family x) ;
  end;
rule LeftExists ↪ LeftExistsProof;

symbol RightExistsProof Γ ϕ t Δ : prf (seq Γ ((ϕ t) ⸬ Δ) ) → prf (seq Γ ((Exists ϕ) ⸬ Δ)) ≔
  begin
    assume Γ ϕ t Δ p;
    refine RightNot Γ (Forall (λ x, (Neg (ϕ x)))) Δ _;
    refine LeftForall Γ (λ x, (Neg (ϕ x))) t Δ _;
    refine LeftNot Γ (ϕ t) Δ p;
  end;

rule RightExists ↪ RightExistsProof;

symbol RightExistsOneProof Γ ϕ Δ :  prf (seq Γ ((Exists (λ y : Term, (Forall (λ x : Term, (Iff (Equality x y) (ϕ x)))))) ⸬ Δ)) → prf (seq Γ ((ExistsOne ϕ) ⸬ Δ)) ≔ RightExistsOne Γ ϕ Δ;


symbol LeftExistsOneProof Γ ϕ Δ : prf (seq ((Exists (λ y : Term, (Forall (λ x : Term, (Iff (Equality x y) (ϕ x)))))) ⸬ Γ) Δ) → 
                                      prf (seq ((ExistsOne ϕ ⸬ Γ)) Δ) ≔ LeftExistsOne Γ ϕ Δ;






/*

symbol LeftAnd Γ l Δ : prf (seq (l ∪ Γ) Δ) → prf (seq ((set2and l) ** Γ) Δ);
symbol LeftOr Γ Σ Δ Ω ϕ ψ : prf (seq (ϕ ** Γ) Δ) → prf (seq  (ψ ** Σ) Ω) → prf (seq ((ϕ ∨ ψ) ** (Γ ∪ Σ)) (Δ ∪ Ω));
constant symbol LeftImplies Γ Σ Δ Ω ϕ ψ :  prf (seq Γ (ϕ ** Δ)) → prf (seq (ψ ** Σ) Ω) → prf (seq ((Implies ϕ ψ) ** (Γ ∪ Σ)) (Δ ∪ Ω));
symbol LeftIff Γ ϕ ψ Δ : prf (seq ((Implies ϕ ψ) ** (Implies ψ ϕ) ** Γ) Δ) → prf (seq ((Iff ϕ ψ) ** Γ) Δ);
symbol LeftNot Γ ϕ Δ : prf (seq Γ (ϕ ** Δ)) → prf (seq ( (Neg ϕ) ** Γ) Δ);
constant symbol LeftForall Γ ϕ t Δ : prf (seq ((ϕ t) ** Γ) Δ) → prf (seq ((Forall ϕ) ** Γ) Δ);
symbol LeftExists Γ ϕ Δ : (Π x:Term, prf (seq ((ϕ x) ** Γ) Δ)) → prf (seq ((Exists ϕ) ** Γ) Δ);
symbol LeftExistsOne Γ ϕ Δ : prf (seq ((Exists (λ y : Term, (Forall (λ x : Term, (Iff (Equality x y) (ϕ x)))))) ** Γ) Δ) → prf (seq ((ExistsOne ϕ ** Γ)) Δ);






*/

/*

symbol fprf : Formula → TYPE;
constant symbol Nothing : TYPE;
symbol not2 ≔ Π (r:TYPE), r;
rule efq $t ↪ Nothing → t;
symbol efq:  Π a, Nothing → τ a;

symbol Truc : TYPE;
symbol efqtruc : Nothing → Truc;

a and b ↪ (a → (b→ Nothing)) → Nothing;

f : ((a → Noting) → Nothing) → a;



symbol Something ≔ Nothing → Nothing;
symbol Some ≔ λ (x : Nothing), x;


rule fprf (Neg $x) ↪ fprf $x → Nothing;
rule fprf (Implies $x $y) ↪ fprf $x → fprf $y;



rule prf (seq Nil Nil) ↪ Nothing;
rule prf (seq Nil ($x ⸬ $l)) ↪ ((fprf $x) → Nothing) → (prf (seq Nil $l));
rule prf (seq ($x ⸬ $l1) $l2) ↪ (fprf $x) → (prf (seq $l1 $l2));
type Hypothesis;
type λ ϕ, (Hypothesis ϕ Nil Nil);
compute Π ϕ: τ formula, prf (seq (ϕ ⸬ Nil) (ϕ ⸬ Nil));

//Π ϕ: Formula, fprf ϕ → (fprf ϕ → Nothing) → Nothing λ x h1 h2, h2 h1
rule Hypothesis $ϕ Nil Nil ↪  λ (h1 : fprf $ϕ) (h2 : fprf $ϕ → Nothing), h2 h1;
type λ ϕ x l, Hypothesis ϕ Nil (x ⸬ l);
compute Π ϕ: τ formula, Π x: τ formula, Π l: List formula, prf (seq (ϕ ⸬ Nil) (ϕ ⸬ (x ⸬ l)));
 //Π ϕ: Formula, Π x: Formula, Π l: List formula, fprf ϕ → (fprf ϕ → Nothing) → (fprf x → Nothing) → prf (seq Nil l)
//rule Hypothesis $ϕ Nil ($x ⸬ $l) ↪
*/
