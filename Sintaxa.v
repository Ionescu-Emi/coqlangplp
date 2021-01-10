Require Import String.
Scheme Equality for string.
Definition Var := string.
Open Scope string_scope.

Inductive Val : Type :=
|  num: nat -> Val
| boolean : bool -> Val
|undefined
|error.


Compute undefined.
Compute num 3.
Coercion num : nat >-> Val.
Coercion boolean : bool >-> Val.
Definition Env := Var -> Val.
Definition env1 : Env :=
  fun x =>
    if (string_eq_dec x "trei")
    then 10
    else undefined.
Definition update (env : Env)
           (x : Var) (v : Val) : Env :=
  fun y =>
    if (string_eq_dec y x)
    then v
    else (env y).
Compute update env1 "trei" true "trei".
Notation "S [ V /' X ]" := (update S X V) (at level 0).



Inductive AExp :=
| avar : Var -> AExp
| anum : Val -> AExp
| aplus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amodulo : AExp -> AExp -> AExp
| aminus : AExp -> AExp -> AExp.
Notation "A +' B" := (aplus A B) (at level 48).
Notation "A -' B" := (aminus A B) (at level 48).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A //' B" := (adiv A B) (at level 46).
Notation "A %' B" := (amodulo A B) (at level 46).
Coercion anum : Val >-> AExp.
Coercion avar : Var >-> AExp.
Definition additionop (n1 n2 : Val) : Val :=
  match n1, n2 with
| num a, num b => a + b
| error , _ => error
| _ , error => error
| _ , _ => undefined
end.
Definition multiplicationop (n1 n2 : Val) : Val :=
  match n1, n2 with
| num a, num b => a * b
| error , _ => error
| _ , error => error
| _ , _ => undefined
end.
Definition divisionop (n1 n2 : Val) : Val :=
  match n1, n2 with
| num a, num b => Nat.div a b
| error , _ => error
| _ , error => error
| _ , _ => undefined
end.
Definition minusop (n1 n2 : Val) : Val :=
  match n1, n2 with
| num a, num b => a - b
| error , _ => error
| _ , error => error
| _ , _ => undefined
end.
Definition moduloop (n1 n2 : Val) : Val :=
  match n1, n2 with
| num a, num b => Nat.modulo a b
| error , _ => error
| _ , error => error
| _ , _ => undefined
end.
Definition lessthaneq (n1 n2 : Val) : bool :=
  match n1, n2 with
| num a, num b => Nat.leb a b
| error , _ => false
| _ , error => false
| _ , _ => false
end.
Definition lessthan (n1 n2 : Val) : bool :=
  match n1, n2 with
| num a, num b => Nat.ltb a b
| error , _ => false
| _ , error => false
| _ , _ => false
end.



Fixpoint aeval_fun (a : AExp) (env : Env) : Val :=
  match a with
  | avar k => env k
  | anum v => v
  | aplus a1 a2 => additionop (aeval_fun a1 env) (aeval_fun a2 env)
  | amul a1 a2 => multiplicationop (aeval_fun a1 env) (aeval_fun a2 env)
  | adiv a1 a2 => divisionop (aeval_fun a1 env) (aeval_fun a2 env)
  | aminus a1 a2 => minusop (aeval_fun a1 env) (aeval_fun a2 env)
  | amodulo a1 a2 => moduloop (aeval_fun a1 env) (aeval_fun a2 env)
  end.




Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| blessthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp.

Notation "A <=' B" := (blessthan A B) (at level 53).
Reserved Notation "B ={ S }=> B'" (at level 70).

Inductive Exp :=
|AExpto : AExp -> Exp
|BExpto : BExp -> Exp.
Coercion AExpto : AExp >-> Exp.
Coercion BExpto : BExp >-> Exp.



Inductive Stmt :=
| assignment : Var -> Exp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| fors : Stmt -> BExp -> Stmt -> Stmt -> Stmt
| int : Var -> Stmt
| bools : Var -> Stmt
| vec_int : Var -> nat -> Stmt
| vec_bools : Var -> nat -> Stmt
| vec_access : Var -> nat -> Stmt
| function_call : Var -> list Val -> Stmt
| function_definition : Var -> nat -> Stmt -> Stmt
| class' : Var -> Stmt -> Stmt
| object_declaration : Var -> Var -> Stmt
| class_var_access : Var -> Var -> Stmt
| class_method_call : Var -> Var -> list Val -> Stmt.

Notation "X ::= A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "'int' A" := (int A) (at level 50).
Notation "'bool' A" := (bools A) (at level 50).
Check bool "trei".
Notation "'if' ( B ) {{ S }}" := ( ifthen B S) (at level 50).
Notation "'if2' ( B ) {{ S1 }} {{ S2 }}" := ( ifthenelse B S1 S2) (at level 50).

Check ( 
  if2 (btrue) {{
   "sapte" ::= 3 }}
  {{ "sapte" ::= 4 }} ).
Notation " 'for' ( S1 ; B ; S2 ) {{ S }} " := (fors S1 B S2 S) (at level 50).
Check (
   for ( "trei" ::= 4 ;bfalse;"trei"::= avar "trei" +' 1 )
      {{    "sapte" ::= 4 }} ).


Notation "'while' ( B ) {{ S }}" := ( while B S) (at level 50).

Notation "'int' V [[ i ]] " := ( vec_int V i )(at level 50).
Check ( int "trei"[[2]] ) .
Notation "'bool' B [[ i ]] " := ( vec_bools B i )(at level 50).
Notation "V [[ i ]] " := ( vec_access V i )(at level 50).
Notation "f (( Vars ))" :=( function_call f Vars ) (at level 50).
Check ( "F"((nil)) ).
Notation "f ((

