constant symbol Set : TYPE;

// Interpretation of set codes in TYPE

injective symbol τ : Set → TYPE; // `t or \tau

constant symbol List:Π a:Set, TYPE;
constant symbol Nil [a] : List a;
symbol ⸬   [a] : τ a → List a → List a;

notation ⸬ infix right 20;

symbol append [a] : List a → List a → List a;

rule append Nil       $l  ↪ $l;
rule append ($x ⸬ $l) $l2 ↪ $x ⸬ (append $l $l2);
rule append $Γ Nil ↪ $Γ;


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

symbol reverse [a] : List a → List a → List a;
rule reverse Nil $acc ↪ $acc;
rule reverse ($x ⸬ $xs) $acc ↪ reverse $xs ($x ⸬ $acc);



//insert an element at a given place in a list
symbol insert [a] : τ a → List a → Nat → List a;
rule insert $x ($y ⸬ $l) O ↪ $x ⸬ $l;
rule insert $x Nil O ↪ $x ⸬ Nil;
rule insert $x Nil (S $z) ↪ $x ⸬ (insert $x Nil $z); 
rule insert $x ($y ⸬ $l) (S $z) ↪ $y ⸬ (insert $x $l $z);

// count elements in a list and replace them by their index
symbol enumerate [a] :  Nat → List a → List nat ;
rule enumerate $n Nil ↪ Nil;
rule enumerate $n ($x ⸬ $l) ↪ $n ⸬ (enumerate (S $n) $l);


symbol swap-multi [a] : List nat → List a → List a → List a;
rule swap-multi Nil $Γ $acc ↪ append $acc $Γ;
rule swap-multi  ($i ⸬ $il) ($v ⸬ $vl) $acc ↪ swap-multi $il $vl (insert $v $acc $i) ;

//symbol equal-int-lists : List nat → List nat → Nat;
//rule equal-int-lists Nil Nil ↪ 0;
//rule equal-int-lists ($x ⸬ $xs) Nil ↪ 1;
//rule equal-int-lists Nil ($y ⸬ $ys) ↪ 1;
//rule equal-int-lists (0 ⸬ $xs) (0 ⸬ $ys) ↪ equal-int-lists $xs $ys;
//rule equal-int-lists (0 ⸬ $xs) ((S $m) $ys) ↪ 1;
//rule equal-int-lists  ((S $n) ⸬ xs) (0 $ys) ↪ 1;
//rule equal-int-lists ((S $n) ⸬ xs) ((S $m) ⸬ ys) ↪ equal-int-lists ($n ⸬ $xs) ($m ⸬ $ys);

symbol is-natural : List nat → Nat → Nat;
rule is-natural Nil $n ↪ 0;
rule is-natural ($n ⸬ $xs)  $n ↪ is-natural $xs (S $n);

symbol is-perm : List nat → Nat;
rule is-perm $l ↪ is-natural (swap-multi $l $l $l) 0;


symbol permute [a] : List nat → List a → List a → List a;
symbol permute2 [a] : Nat → List nat → List a → List a → List a;

rule permute $ln $l $acc ↪ permute2 (is-perm $ln) $ln $l $acc;
rule permute2 0 $ln $l $acc ↪ swap-multi $ln $l $acc;

//correct permutation
compute permute (1 ⸬ 0 ⸬ 2 ⸬ Nil) (42 ⸬ 50 ⸬ 167 ⸬ 21 ⸬ 17 ⸬ Nil) Nil;
compute permute (3 ⸬ 0 ⸬ 2 ⸬ 1 ⸬ 4 ⸬ Nil) (3 ⸬ 0 ⸬ 2 ⸬ 1 ⸬ 4 ⸬ Nil) Nil;
compute permute (1 ⸬ 0 ⸬ 2 ⸬ 3 ⸬ Nil) (42 ⸬ 50 ⸬ 167 ⸬ 21 ⸬ 17 ⸬ Nil) Nil;

//incorrect permutation
compute permute (3 ⸬ 0 ⸬ 2 ⸬ Nil) (42 ⸬ 50 ⸬ 167 ⸬ 21 ⸬ 17 ⸬ Nil) Nil;

//correct cases
compute is-perm Nil;
compute is-perm (0 ⸬ Nil);
compute is-perm (0 ⸬ 1 ⸬ 2 ⸬ 3 ⸬ 4 ⸬ Nil);
compute is-perm (4 ⸬ 3 ⸬ 2 ⸬ 1 ⸬ 0 ⸬ Nil);
compute is-perm (1 ⸬ 4 ⸬ 3 ⸬ 0 ⸬ 2 ⸬ Nil);

//incorrect cases
compute is-perm (1 ⸬ 4 ⸬ 3 ⸬ 0 ⸬ 2 ⸬ 1 ⸬ Nil);
compute is-perm (1 ⸬ 4 ⸬ 0 ⸬ 2 ⸬ 1 ⸬ Nil);
compute is-perm (1 ⸬ 4 ⸬ 6 ⸬ 3 ⸬ 0 ⸬ 2 ⸬ Nil);
compute is-perm (1 ⸬ 4 ⸬ 3 ⸬ 0 ⸬ Nil);

symbol swap [a] : List a → Nat → List a;
rule swap Nil            _      ↪ Nil;
rule swap ($x ⸬ Nil)     _      ↪ $x ⸬ Nil;
rule swap ($x ⸬ $y ⸬ $l) 0      ↪ ($y ⸬ $x ⸬ $l);
rule swap ($x ⸬ $y ⸬ $l) (S $n) ↪ ($x ⸬ (swap ($y ⸬ $l) $n));
