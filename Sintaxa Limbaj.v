(* Pentru Variabile *)

Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.
Require Import Ascii.
Check length("alex").
Compute length("alex").
Check nat.
Inductive NaturalV :=
| eroare_nat : NaturalV
| numar : nat -> NaturalV.
Check NaturalV.
Check numar 3.
Inductive BooleanV :=
| eroare_bool : BooleanV
| boolean : bool -> BooleanV.
Check boolean false.
Inductive CharV :=
| eroare_char : CharV
| caracter : ascii -> CharV.
Check caracter "v".
Scheme Equality for CharV.
Coercion numar : nat >-> NaturalV.
Coercion boolean: bool >-> BooleanV.
Coercion caracter: ascii >-> CharV. 
Inductive Stiva ( tip : Set ) : Set :=
| stiva_vida : Stiva tip
| stiva_nevida : tip -> Stiva tip -> Stiva tip.
Check Stiva.
Check Stiva nat.
Check Stiva bool.
Check (stiva_nevida nat 6 (stiva_vida nat)) .
Check stiva_nevida bool false (stiva_vida bool).
Check (stiva_nevida nat 3 ( stiva_nevida nat 2  (stiva_vida nat)  ) ).
Check stiva_vida NaturalV.
Check CharV.
Check Stiva CharV.
Definition Stiva_Push  (x:Set)( L : Stiva x ) ( p : x ) : Stiva x :=
match L with
| _ => (stiva_nevida x p L )
end.
Compute (Stiva_Push nat (stiva_vida nat) 3). 
Compute (Stiva_Push CharV (stiva_vida CharV) (caracter "r") ).

Definition Stiva_Pop  (x:Set)( L : Stiva x ) : Stiva x :=
match L with 
| stiva_nevida _ p L' => L'
| _ =>stiva_vida x
end.
Compute Stiva_Pop nat ( stiva_vida nat ).
Compute Stiva_Pop nat (stiva_nevida nat 6 ( stiva_vida nat )).
Compute Stiva_Pop nat (stiva_nevida nat 7 (stiva_nevida nat 6 ( stiva_vida nat ))).

Definition Stiva_Top (x:Set)(eroare:x)(L : Stiva x) : x :=
match L with
| stiva_nevida _ p _  => p
| stiva_vida _ => eroare
end.

Compute (Stiva_Top NaturalV eroare_nat  (stiva_nevida NaturalV 6 ( stiva_vida NaturalV )) ).
Check (Stiva_Top NaturalV eroare_nat  (stiva_nevida NaturalV 6 ( stiva_vida NaturalV )) ).
Compute (Stiva_Top NaturalV eroare_nat  (stiva_vida NaturalV) ).

Fixpoint nrelem_stiva (X: Set)(L : Stiva X ) : nat :=
match L with
| stiva_vida _ => 0
| stiva_nevida _ p L' => 1 + (nrelem_stiva _ L')
end.  


Compute nrelem_stiva nat (stiva_vida nat).
Compute nrelem_stiva nat (stiva_nevida nat 3 (stiva_vida nat)).

Fixpoint alipire_stive (X: Set) (L1 : Stiva X ) (L2 : Stiva X ) : Stiva X :=
match L1 with  
| _ =>match L2 with |stiva_vida _ => L1
                    | stiva_nevida _ p L=> (alipire_stive _ (Stiva_Push _ L1 p) L)
                       end
end.

Compute alipire_stive nat (stiva_vida nat)(stiva_nevida nat 7 (stiva_nevida nat 6 ( stiva_vida nat ))).
Compute alipire_stive nat (stiva_nevida nat 7 (stiva_nevida nat 6 ( stiva_vida nat ))) (stiva_nevida nat 7 (stiva_nevida nat 6 ( stiva_vida nat ))).
Definition concat_stive (X: Set) (L1 : Stiva X ) (L2 : Stiva X ) : Stiva X :=
match L1 with
| _ => (alipire_stive _ L1 (alipire_stive _ (stiva_vida _ ) L2 ) )
end.

Compute concat_stive nat (stiva_nevida nat 7 (stiva_nevida nat 6 ( stiva_vida nat ))) (stiva_nevida nat 7 (stiva_nevida nat 6 ( stiva_vida nat ))).
Definition Copie_Stiva (X:Set) (destinatie:Stiva X)(decopiat:Stiva X) : Stiva X :=
match destinatie with 
| _ => concat_stive _ decopiat (stiva_vida _)
end.

Compute (Copie_Stiva nat (stiva_nevida nat 7 (stiva_nevida nat 6 ( stiva_vida nat ))) (stiva_nevida nat 5 (stiva_vida nat)) ) .
                        
Definition strlen (L : Stiva CharV) : nat :=
match L with 
|_ => nrelem_stiva CharV L
end.
Compute strlen ( (stiva_nevida CharV (caracter "a") (stiva_nevida CharV (caracter "b") ( stiva_vida CharV ))) ).

Definition strcpy (destinatie : Stiva CharV)(decopiat : Stiva CharV): Stiva CharV  :=
match destinatie with
| _ => Copie_Stiva CharV destinatie decopiat
end.

Compute (strcpy  (stiva_nevida CharV (caracter "a") (stiva_nevida CharV (caracter "b") ( stiva_vida CharV ))) (stiva_vida CharV)).

Definition strcat (destinatie : Stiva CharV)(decopiat : Stiva CharV): Stiva CharV  :=
match destinatie with 
| _ => concat_stive CharV destinatie decopiat
end.
Compute (strcat  (stiva_nevida CharV (caracter "a") (stiva_nevida CharV (caracter "b") ( stiva_vida CharV ))) (stiva_vida CharV)).

Fixpoint strchr (L : Stiva CharV)(carac : CharV) : bool :=
match L with 
|stiva_vida _ => false
|stiva_nevida _ p L'=> if(CharV_beq ( Stiva_Top _ eroare_char L) carac) then true else (strchr L' carac) 
end.
Compute (strchr  (stiva_nevida CharV (caracter "a") (stiva_nevida CharV (caracter "b") ( stiva_vida CharV ))) (caracter "d")).
Compute (strchr  (stiva_nevida CharV (caracter "a") (stiva_nevida CharV (caracter "b") ( stiva_vida CharV ))) (caracter "d")).
(*
Inductive Vector ( tip : Type ) : nat-> Type :=
| vector_vid : Vector tip 0
| vector_nevid : tip -> forall n , Vector tip n -> Vector tip (S n).

Check Vector.
Check vector_vid.
Check vector_vid nat .
Check (vector_nevid nat 3 0 ( vector_vid nat )) .
Check  (vector_nevid nat 3 1 (vector_nevid nat 3 0 ( vector_vid nat ))) .
Check Vector nat 2.
Check Stiva nat.
Check vector_nevid nat 3 0.
(* pentru a arata elementul de pe ultima pozitie*)
Definition UltimaPozitie ( x : Set ) i ( v : Vector x (S i) ) : x :=
match v with 
| vector_nevid _ a _ _ => a
end.

Compute (UltimaPozitie nat 1 (vector_nevid nat 5 1 (vector_nevid nat 3 0 ( vector_vid nat ))) ).

Compute (UltimaPozitie nat 2 (vector_nevid nat 6 2 (vector_nevid nat 5 1 (vector_nevid nat 3 0 ( vector_vid nat )))) ).
(* similiar ca stiva *)
Definition Vector_pop (X : Set) n (v : Vector X (S n)) : Vector X n :=
match v with
| vector_nevid  _ _ _ tl => tl
  end.


Compute (Vector_pop nat 1 (vector_nevid nat 5 1 (vector_nevid nat 3 0 ( vector_vid nat ))) ).*)

Inductive Pair : Type := 
|pereche : Type  -> string -> Pair.

Check pereche nat "ar" .

Inductive Struct : Type :=
|struct_vid : Struct 
|struct_nevid : Pair -> Struct ->Struct.

Check Struct.
Check struct_vid.
Check (struct_nevid (pereche bool "b")(struct_nevid (pereche nat "a") struct_vid)).

Require Import Nat.
(* tipul general de date *)
Inductive Rvalue := 
| eroare_nedeclarare : Rvalue
| eroare_asignare : Rvalue
| default_char : Rvalue
| default_nat : Rvalue
| default_bool : Rvalue
| cons_nat : NaturalV-> Rvalue
| cons_bool : BooleanV -> Rvalue
| cons_char : CharV -> Rvalue
| cons_stiva_nat : (Stiva NaturalV) -> Rvalue
| cons_stiva_bool : (Stiva BooleanV) -> Rvalue
| cons_stiva_char : (Stiva CharV) -> Rvalue
| cons_struct : Struct -> Rvalue.
Check cons_nat.
Check NaturalV.
Definition Env : string -> Rvalue.
Definition acelasi_tip ( r1 : Rvalue)(r2 : Rvalue) : bool :=
match r1 with 
| eroare_nedeclarare => match r2 with |eroare_nedeclarare =>true
                                      |_ => false 
                                       end
| eroare_asignare=>match r2 with |eroare_asignare => true
                                 |_ =>false 
                                  end
| default_char => match r2 with |default_char => true
                                |_ =>false 
                                 end
| default_nat => match r2 with|default_nat => true
                              |_=> false
                               end
| default_bool => match r2 with|default_bool =>true
                              |_=> false end
| cons_nat x => match r2 with |cons_nat y=> true
                              | _ => false end
  
| cons_bool x => match r2 with |cons_bool y=> true
                               | _ => false end
| cons_char x => match r2 with |cons_char y=> true
                              | _ => false end
|cons_stiva_nat x => match r2 with | cons_stiva_nat y => true
                                   |_=>false end
|cons_stiva_bool x => match r2 with | cons_stiva_bool y => true
                                   | _ =>false end
|cons_stiva_char x => match r2 with | cons_stiva_char y => true
                                   |_=>false end
|cons_struct x => match r2 with | cons_struct y => true
                                | _ => false end
end.
Compute acelasi_tip ( default_char) ( default_bool ).
Compute acelasi_tip (cons_nat 100) (cons_bool false).
Compute acelasi_tip (cons_nat 100) (cons_nat 4).



Inductive AExp :=
| avar : string -> AExp
| anum : NaturalV -> AExp
| aplus : AExp -> AExp -> AExp
| asub : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.

Notation "A +' B" := (aplus A B) (at level 50,left associativity).
Notation "A *' B" := (amul A B) (at level 48,left associativity).
Notation "A -' B" := (asub A B) (at level 50,left associativity).
Notation "A /' B" := (adiv A B) (at level 48,left associativity).
Notation "A %' B" := (amod A B) (at level 50,left associativity).
Coercion anum : NaturalV >-> AExp.
Coercion avar : string >-> AExp.

Check 2 +' 3.
Check "sa" +' "bs".
Check avar "a".
Check (3 -' "a") *' 2.
Check 2 +' (Stiva_Top NaturalV eroare_nat  (stiva_nevida NaturalV 6 ( stiva_vida NaturalV )) ).


Inductive BExp :=
| beroare : BExp
| btrue : BExp
| bfalse : BExp
| bvar : string -> BExp
| blessthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.

Notation "A <=' B" := (blessthan A B) (at level 70).
Notation " !' A" := (bnot A) (at level 51,left associativity).
Notation "A &&' B" := (band A B) (at level 52,left associativity).
Notation "A ||' B" := (bor A B) (at level 53,left associativity).

Check beroare.
Check bfalse.
Check !' bfalse.
Check bvar "A".
Check 1 <=' 2.
Check bvar "a" ||' bvar "b".
Check NaturalV.
Inductive Stmt :=
|declare_stiva_nat : string -> Stiva NaturalV -> Stmt 
|declare_stiva_bool : string -> Stiva BooleanV -> Stmt 
|declare_stiva_char : string -> Stiva CharV -> Stmt 
|declare_struct :string ->  Struct -> Stmt
|push_stiva_nat : string -> NaturalV->Stmt
|push_stiva_bool : string -> BooleanV->Stmt
|push_stiva_char : string -> CharV->Stmt
|pop_stiva_nat : string->Stmt
|pop_stiva_bool : string->Stmt
|pop_stiva_char : string->Stmt
|concat_stive_nat : string->string->Stmt
|concat_stive_bool : string->string->Stmt
|stmt_strcat : string->string ->Stmt
|copy_stive_nat : string->string->Stmt
|copy_stive_bool : string->string->Stmt
|stmt_strcpy : string->string ->Stmt
|update_struct_value : string -> string -> Rvalue -> Stmt
|get_struct_value : string -> string -> Type -> Stmt
|declare_nat : string -> AExp -> Stmt
|declare_bool : string -> BExp -> Stmt
|declare_char : string -> CharV -> Stmt
|assign_nat : string -> AExp -> Stmt
|assign_bool : string -> BExp -> Stmt
|assign_char : string -> CharV -> Stmt
|secventa : Stmt -> Stmt -> Stmt
|ifthen : BExp -> Stmt -> Stmt
|ifthenelse :BExp -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| my_for : Stmt -> BExp -> Stmt -> Stmt -> Stmt
| switch : BExp -> BExp -> Stmt ->BExp -> Stmt -> Stmt 
| continue : Stmt
| break : Stmt.
Notation "'DSNAT' X :sn= S " := (declare_stiva_nat X S) (at level 50).
Notation "'DSBOOL' X :sb= S " := (declare_stiva_bool X S) (at level 50).
Notation "'DSCHAR' X :sc= S " := (declare_stiva_char X S) (at level 50).
Notation " 'DSTRUCT' X :struct= S" :=(declare_struct X S) (at level 50). 
Notation "X :n= A" := (assign_nat X A) (at level 50).
Notation "X :b= A" := (assign_bool X A) (at level 50).
Notation "X :c= A" := (assign_char X A) (at level 50).
Notation "'DNAT' X ::= A" := (declare_nat X A) (at level 50).
Notation "'DBOOL' X ::= A" := (declare_bool X A) (at level 50).
Notation "'DCHAR' X ::= A" := (declare_char X A) (at level 50).
Notation " S1 ;; S2 " := (secventa S1 S2) (at level 50).
Notation " 'strcat'' ( S1 , S2 ) " := (stmt_strcat S1 S2) (at level 50 ).
Notation " 'strcpy'' ( S1 , S2 ) " := (stmt_strcpy S1 S2) (at level 50 ).
Notation "S .=' F T" :=(get_struct_value S F T) (at level 50).
Check (get_struct_value "struct" "a" bool ).
Check DNAT "X" ::= 3.
Check "var" :c= caracter "a".
Check ifthen (0 <=' 3) ( "alex" :n= (3 +' 4) ).
Check switch ( bfalse ||' btrue ) btrue ( "i" :n= 2 ) bfalse ( "i" :n= 3).
Definition prgrm :=
DSNAT "stiva" :sn= (stiva_vida NaturalV)  ;;
push_stiva_nat "stiva" 3 ;;
pop_stiva_nat "stiva" ;;
DSCHAR "stiva1" :sc= (stiva_vida CharV)  ;;
push_stiva_char "stiva1" (caracter "r") ;;
DSCHAR "stiva2" :sc= (stiva_vida CharV)  ;;
push_stiva_char "stiva2" (caracter "p") ;;
strcat' ( "stiva1" , "stiva2" ) ;;
strcpy' ( "stiva1" , "stiva2" ) ;;
DNAT "x" ::= 3 ;;
DNAT "suma" ::=0 ;;
(my_for (DNAT "i" ::= 1 ) ( "i" <=' "x" ) ( "i":n=("i" +' 1) ) ( "sum":n=("sum" +' 1) )) ;;
DCHAR "var" ::= (caracter "a") .

Definition program_switch :=
DSTRUCT "o" :struct= (struct_vid) ;;
DNAT "C" ::= 3 ;;
switch ( "C" <=' 4 )
    (btrue) ("C" :n= ("C" +' 1) )
    (bfalse) ("C" :n=("C" -' 1) ).

Definition program_break :=
DNAT "a" ::= 5 ;;
DBOOL "b" ::= bfalse ;;
while ( 0 <=' "a" )
   (ifthen ( bvar "b" &&' bfalse ) break ;;
   ("a" :n= ("a" -' 1)) ).
  










