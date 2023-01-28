constant symbol Set : TYPE;

// Interpretation of set codes in TYPE

injective symbol τ : Set → TYPE; // `t or \tau

constant symbol List:Π a:Set, TYPE;
constant symbol Nil [a] : List a;
symbol ⸬   [a] : τ a → List a → List a;

notation ⸬ infix right 20;

symbol append [a] : List a → List a → List a;

rule append Nil $l ↪ $l;
rule append ($x ⸬ $l) $l2 ↪ $x ⸬ (append $l $l2);


constant symbol Nat : TYPE;

constant symbol O : Nat ;
constant symbol S  : Nat → Nat;


builtin "0"  ≔ O;
builtin "+1" ≔ S;

constant symbol nat : Set;

rule τ nat ↪ Nat;

symbol map [a] [b] : (τ a → τ b) → List a → List b ;
rule map _ Nil ↪ Nil;
rule map $f ($x ⸬ $l) ↪ ($f $x) ⸬ (map $f $l);

symbol insert [a] : τ a → List a → Nat → List a;
rule insert $x ($y ⸬ $l) O ↪ $x ⸬ $l;
rule insert $x Nil O ↪ $x ⸬ Nil;
rule insert $x Nil (S $z) ↪ $x ⸬ (insert $x Nil $z); 
rule insert $x ($y ⸬ $l) (S $z) ↪ $y ⸬ (insert $x $l $z);

symbol swap-multi [a] : List nat → List a → List a → List a;
rule swap-multi Nil Nil $acc ↪ $acc;
rule swap-multi ($i ⸬ $il) ($v ⸬ $vl) $acc ↪ swap-multi $il $vl (insert $v $acc $i) ;

compute swap-multi (3 ⸬ 0 ⸬ 2 ⸬ 1 ⸬ 4 ⸬ Nil) (42 ⸬ 50 ⸬ 167 ⸬ 21 ⸬ 17 ⸬ Nil) Nil;


