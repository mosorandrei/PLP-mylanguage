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
Check EmptyString.
Fixpoint GetV (S : Struct)(x : string) : string :=
match S with 
|struct_vid => ""
|(struct_nevid ( pereche tip sir) s') => if ( string_beq  sir x ) then sir else GetV s' x
end.
Compute GetV (struct_nevid (pereche bool "b")(struct_nevid (pereche nat "a") struct_vid)) "a".
Require Import Nat.
(* tipul general de date *)
Inductive Rvalue := 
| eroare_nedeclarare : Rvalue
| eroare_asignare : Rvalue
| cons_nat : NaturalV-> Rvalue
| cons_bool : BooleanV -> Rvalue
| cons_char : CharV -> Rvalue
| cons_stiva_nat : (Stiva NaturalV) -> Rvalue
| cons_stiva_bool : (Stiva BooleanV) -> Rvalue
| cons_stiva_char : (Stiva CharV) -> Rvalue
| cons_struct : Struct -> Rvalue.
Check cons_stiva_nat (stiva_vida NaturalV).
Check cons_nat.
Check NaturalV.
Definition Env := string -> Rvalue.
Definition env0 : Env := fun x => eroare_nedeclarare.
Definition acelasi_tip ( r1 : Rvalue)(r2 : Rvalue) : bool :=
match r1 with 
| eroare_nedeclarare => match r2 with |eroare_nedeclarare =>true
                                      |_ => false 
                                       end
| eroare_asignare=>match r2 with |eroare_asignare => true
                                 |_ =>false 
                                  end
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

Compute acelasi_tip (cons_nat 100) (cons_bool false).
Compute acelasi_tip (cons_nat 100) (cons_nat 4).

Definition update (env : Env) ( x: string ) ( v : Rvalue ) : Env :=
fun y =>
 if(string_beq x y)
  then 
      if ( andb ( acelasi_tip (env y) eroare_nedeclarare) true )
                       then  v
         else if (andb ( acelasi_tip (env y) v) true ) then v else eroare_asignare 
 else (env y).
Notation "S [ V /' X ]" := (update S X V) ( at level 0).
Compute (env0 "x").
Compute (update env0 "x" (cons_stiva_nat (stiva_vida NaturalV))).
Compute ((update env0 "x" (cons_stiva_nat (stiva_vida NaturalV))) "x").


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
Definition plus_natural ( A1 A2 : NaturalV ) : NaturalV :=
match A1,A2 with 
| _ ,eroare_nat => eroare_nat 
| eroare_nat , _ => eroare_nat
| numar n1 , numar n2 => numar (n1 + n2)
end.

Compute plus_natural eroare_nat (numar 2).
Compute plus_natural (numar 2) (numar 2).
Compute plus_natural 1 eroare_nat.

Definition minus_natural ( A1 A2 : NaturalV ) : NaturalV :=
match A1,A2 with 
| _ ,eroare_nat => eroare_nat 
| eroare_nat , _ => eroare_nat
| numar n1 , numar n2 =>if(ltb n1 n2) then eroare_nat else numar (n1 - n2)
end.

Compute minus_natural 1 eroare_nat.
Compute minus_natural 1 3.
Compute minus_natural 5 0.

Definition mul_natural ( A1 A2 : NaturalV ) : NaturalV :=
match A1,A2 with 
| _ ,eroare_nat => eroare_nat 
| eroare_nat , _ => eroare_nat
| numar n1 , numar n2 => numar (n1 * n2)
end.

Compute mul_natural 1 3.

Definition div_natural ( A1 A2 : NaturalV ) : NaturalV :=
match A1,A2 with 
| _ ,eroare_nat => eroare_nat 
| eroare_nat , _ => eroare_nat
| _ , numar 0 => eroare_nat
| numar n1 , numar n2 => numar (div n1 n2)
end.


Compute div_natural 1 3.
Compute div_natural 1 0.

Definition mod_natural ( A1 A2 : NaturalV ) : NaturalV :=
match A1,A2 with 
| _ ,eroare_nat => eroare_nat 
| eroare_nat , _ => eroare_nat
| _ , numar 0 => eroare_nat
| numar n1 , numar n2 => numar ( n1 - n2*(div n1 n2))
end.

Compute mod_natural 1 3.
Compute mod_natural 1 0.

Reserved Notation "A =[ S ]=> N" (at level 60).

Inductive aeval : AExp -> Env -> NaturalV -> Prop :=
| const : forall c sigma , anum c =[ sigma ]=> c
| var : forall c sigma , avar c =[ sigma ]=> match (sigma c) with | cons_nat x => x
                                                                  | _ => eroare_nat end
| add : forall a1 a2 n1 n2 x sigma,
 a1 =[ sigma ]=> n1 ->
 a2 =[ sigma ]=> n2 ->
 x = (plus_natural n1 n2) ->
 a1 +' a2 =[ sigma ]=> x
| minus : forall a1 a2 n1 n2 x sigma,
 a1 =[ sigma ]=> n1 ->
 a2 =[ sigma ]=> n2 ->
 x = (minus_natural n1 n2) ->
 a1 -' a2 =[ sigma ]=> x
| mul : forall a1 a2 n1 n2 x sigma,
 a1 =[ sigma ]=> n1 ->
 a2 =[ sigma ]=> n2 ->
 x = (mul_natural n1 n2) ->
 a1 *' a2 =[ sigma ]=> x
| my_div : forall a1 a2 n1 n2 x sigma,
 a1 =[ sigma ]=> n1 ->
 a2 =[ sigma ]=> n2 ->
 x = (div_natural n1 n2) ->
 a1 /' a2 =[ sigma ]=> x
| my_mod : forall a1 a2 n1 n2 x sigma,
 a1 =[ sigma ]=> n1 ->
 a2 =[ sigma ]=> n2 ->
 x = (mod_natural n1 n2) ->
 a1 %' a2 =[ sigma ]=> x
where "A =[ S ]=> N" := (aeval A S N).

Example ex1 : 3 +' 7 =[ env0 ]=>10.
Proof. 
eapply add.
eapply const. 
eapply const.
simpl.
reflexivity.
Qed.
Example ex2 : 3 /' 0 =[ env0 ]=> eroare_nat .
Proof.
eapply my_div.
eapply const.
eapply const.
simpl.
reflexivity.
Qed.
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

Definition mai_mic_egal (A1 A2 : NaturalV) : BooleanV :=
match A1,A2 with
| _ , eroare_nat => eroare_bool
| eroare_nat , _ => eroare_bool
| numar a , numar b => boolean ( leb a b ) end.
Compute mai_mic_egal 3 4.
Compute mai_mic_egal 9 4.
Compute mai_mic_egal eroare_nat 4.

Definition not_b (A : BooleanV) : BooleanV :=
match A with 
| eroare_bool => eroare_bool
| boolean b => boolean (negb b)
end.

Compute not_b true.

Definition my_and (A1 A2 : BooleanV) : BooleanV :=
match A1,A2 with 
| _ , eroare_bool => eroare_bool
| eroare_bool , _ => eroare_bool
| boolean b1, boolean b2 => boolean ( andb b1 b2 )
end.

Compute my_and true false.
Compute my_and true eroare_bool.

Definition my_or (A1 A2 : BooleanV) : BooleanV :=
match A1,A2 with 
| _ , eroare_bool => eroare_bool
| eroare_bool , _ => eroare_bool
| boolean b1, boolean b2 => boolean ( orb b1 b2 )
end.

Compute my_or true false.
Compute my_or true eroare_bool.

Reserved Notation "A -{ S }-> N" (at level 70).
Inductive beval : BExp -> Env -> BooleanV -> Prop  :=
| eroare_b : forall sigma , beroare -{ sigma }-> eroare_bool
| true_b : forall sigma, btrue -{ sigma }-> true
| false_b : forall sigma , bfalse -{ sigma }-> false
| var_b : forall vr sigma , bvar vr -{ sigma }-> match (sigma vr) with | cons_bool x => x
                                                                  | _ => eroare_bool end

| lessthan_b : forall a1 a2 n1 n2 x sigma,
a1 =[ sigma ]=> n1 ->
a2 =[ sigma ]=> n2 ->
x = (mai_mic_egal n1 n2) ->
 a1 <=' a2  -{ sigma }-> x 
| negatie : forall a n b sigma,
a -{ sigma }-> n ->
b = (not_b n) ->
( !' a ) -{ sigma }-> b
| si : forall a1 a2 n1 n2 x sigma,
a1 -{ sigma }-> n1 ->
a2 -{ sigma }-> n2 ->
x = (my_and n1 n2) ->
( a1 &&' a2 ) -{ sigma }-> x  
| sau : forall a1 a2 n1 n2 x sigma,
a1 -{ sigma }-> n1 ->
a2 -{ sigma }-> n2 ->
x = (my_or n1 n2) ->
( a1 ||' a2 ) -{ sigma }-> x 
where "A -{ S }-> N":=(beval A S N).


Example ex3 : btrue &&' btrue -{ env0 }-> true .
eapply si.
eapply true_b.
eapply true_b.
simpl.
reflexivity.
Qed.

Example ex4 : 2 <=' 5 -{ env0 }-> true .
eapply lessthan_b.
eapply const.
eapply const.
simpl.
reflexivity.
Qed.

Example ex5 : eroare_nat <=' 5 -{ env0 }-> eroare_bool .
eapply lessthan_b.
eapply const.
eapply const.
simpl.
reflexivity.








Inductive Stmt :=
|declare_stiva_nat : string -> Stmt 
|declare_stiva_bool : string -> Stmt 
|declare_stiva_char : string -> Stmt 
|declare_struct :string -> Struct -> Stmt
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
|declare_nat : string  -> Stmt
|declare_bool : string  -> Stmt
|declare_char : string  -> Stmt
|assign_nat : string -> AExp -> Stmt
|assign_bool : string -> BExp -> Stmt
|assign_char : string -> CharV -> Stmt
|secventa : Stmt -> Stmt -> Stmt
|ifthen : BExp -> Stmt -> Stmt
|ifthenelse :BExp -> Stmt ->Stmt-> Stmt
| while : BExp -> Stmt -> Stmt
| my_for : Stmt -> BExp -> Stmt -> Stmt -> Stmt
| switch : BExp -> bool -> Stmt ->bool -> Stmt -> Stmt 
| continue : Stmt
| break : Stmt.
Notation "'DSNAT' X " := (declare_stiva_nat X) (at level 50).
Notation "'DSBOOL' X " := (declare_stiva_bool X) (at level 50).
Notation "'DSCHAR' X " := (declare_stiva_char X) (at level 50).
Notation " 'DSTRUCT' X S " :=(declare_struct X S) (at level 50). 
Notation "X :n= A" := (assign_nat X A) (at level 50).
Notation "X :b= A" := (assign_bool X A) (at level 50).
Notation "X :c= A" := (assign_char X A) (at level 50).
Notation "'DNAT' X " := (declare_nat X) (at level 50).
Notation "'DBOOL' X " := (declare_bool X ) (at level 50).
Notation "'DCHAR' X " := (declare_char X ) (at level 50).
Notation " S1 ;; S2 " := (secventa S1 S2) (at level 60,right associativity).
Notation " 'strcat'' ( S1 , S2 ) " := (stmt_strcat S1 S2) (at level 50 ).
Notation " 'strcpy'' ( S1 , S2 ) " := (stmt_strcpy S1 S2) (at level 50 ).

Check DNAT "X" .
Check "var" :c= caracter "a".
Check ifthen (0 <=' 3) ( "alex" :n= (3 +' 4) ).
Check switch ( bfalse ||' btrue ) true ( "i" :n= 2 ) false ( "i" :n= 3).
Definition prgrm :=
DSNAT "stiva"  ;;
push_stiva_nat "stiva" 3 ;;
pop_stiva_nat "stiva" ;;
DSCHAR "stiva1"  ;;
push_stiva_char "stiva1" (caracter "r") ;;
DSCHAR "stiva2" ;;
push_stiva_char "stiva2" (caracter "p") ;;
strcat' ( "stiva1" , "stiva2" ) ;;
strcpy' ( "stiva1" , "stiva2" ) ;;
DNAT "x" ;;
DNAT "suma" ;;
(my_for ( "i" :n= 1 ) ( "i" <=' "x" ) ( "i":n=("i" +' 1) ) ( "sum":n=("sum" +' 1) )) ;;
DCHAR "v" ;;
("v" :c= (caracter "a")) .

Definition program_switch :=
declare_struct "o" struct_vid ;;
DNAT "C" ;;
switch ( "C" <=' 4 )
    (true) ("C" :n= ("C" +' 1) )
    (false) ("C" :n=("C" -' 1) ).

Definition program_break :=
DNAT "a"  ;;
DBOOL "b" ;;
while ( 0 <=' "a" )
   (ifthen ( bvar "b" &&' bfalse ) break ;;
   ("a" :n= ("a" -' 1)) ).

Reserved Notation "S ~{ Sigma }~> Sigma'"(at level 60).

Inductive eval : Stmt -> Env -> Env ->Prop :=
| d_nat :forall x sigma sigma',  
   sigma' = update sigma x (cons_nat 0) -> 
  (DNAT x) ~{ sigma }~> sigma'
| d_bool :forall x sigma sigma',  
   sigma' = update sigma x (cons_bool false) -> 
  (DBOOL x) ~{ sigma }~> sigma'
| d_char :forall x sigma sigma' , 
   sigma' = (update sigma x (cons_char (caracter "0"))) -> 
  (DCHAR x) ~{ sigma }~> sigma'
| a_nat :forall x a sigma sigma' a',
   a =[ sigma ]=> a' ->  
   sigma' = update sigma x (cons_nat a') -> 
  ( x :n= a) ~{ sigma }~> sigma'
| a_bool :forall x b b' sigma sigma',
   b -{ sigma }-> b' ->  
   sigma' = update sigma x (cons_bool b') -> 
  (x :b= b) ~{ sigma }~> sigma'
| a_char :forall x c sigma sigma' , 
   sigma' = (update sigma x (cons_char c)) -> 
  (x :c= c) ~{ sigma }~> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
s1 ~{ sigma }~> sigma1 ->
s2 ~{ sigma1 }~> sigma2 ->
( s1 ;; s2) ~{ sigma }~> sigma2
|e_ifthen_false : forall b s sigma,
b -{ sigma }->  false ->
(ifthen b s) ~{ sigma }~> sigma 
|e_ifthen_true : forall b s sigma sigma',
b -{ sigma }->  true ->
s ~{ sigma }~> sigma' ->
(ifthen b s) ~{ sigma }~> sigma'
|e_ifthenelse_false : forall b s1 s2 sigma sigma',
b -{ sigma }->  false ->
s2 ~{ sigma }~> sigma' ->
(ifthenelse b s1 s2) ~{ sigma }~> sigma 
|e_ifthenelse_true : forall b s1 s2 sigma sigma',
b -{ sigma }->  true ->
s1 ~{ sigma }~> sigma' ->
(ifthenelse b s1 s2) ~{ sigma }~> sigma'
|e_whilefalse : forall b s sigma,
b -{ sigma }-> false ->
(while b s) ~{ sigma }~> sigma
|e_whiletrue : forall b s sigma sigma',
b -{ sigma }-> true ->
(s ;; while b s) ~{ sigma }~> sigma' ->
(while b s) ~{ sigma }~> sigma'
| for_l :  forall i1 i2 sigma sigma' pas comenzi,
  (i1 ;; (while i2 (comenzi ;; pas ) ) ) ~{ sigma }~> sigma' ->
  (my_for i1 i2 pas comenzi) ~{ sigma }~> sigma'
| e_switch_case1 : forall B b1 b2 i1 i2 sigma sigma1,
B -{ sigma }-> boolean b1 -> 
i1 ~{ sigma }~> sigma1 ->
(switch B b1 i1 b2 i2) ~{ sigma }~> sigma1 
| e_switch_case2 : forall B b1 b2 i1 i2 sigma sigma1,
B -{ sigma }-> boolean b2 -> 
i2 ~{ sigma }~> sigma1 ->
(switch B b1 i1 b2 i2) ~{ sigma }~> sigma1
(* continue si break din bucati *)
| e_break : forall sigma,
break ~{ sigma }~> sigma
| e_while_break_1 : forall  s b sigma sigma', 
b -{ sigma }-> boolean true ->
s~{ sigma }~> sigma' ->
(while b s) ~{ sigma }~> sigma' 
| e_while_continue_1 : forall s s2 b x p sigma sigma', 
s = continue ;; s2 ->
x = p ;; (while b s) ->
p ~{ sigma }~> sigma' -> 
(while b s) ~{ sigma' }~> sigma' 
| e_while_continue_2 : forall s s2 b x p sigma sigma' sigma'', 
s = s2 ;; continue ->
x = p ;; (while b s) ->
p ~{ sigma }~> sigma' -> 
(while b s2) ~{ sigma' }~> sigma'' ->
(while b s) ~{ sigma'}~> sigma''

| ds_nat :forall x sigma sigma',  
   sigma' = update sigma x (cons_stiva_nat (stiva_vida NaturalV)) -> 
  (DSNAT x) ~{ sigma }~> sigma'
| ds_bool :forall x sigma sigma',  
   sigma' = update sigma x (cons_stiva_bool (stiva_vida BooleanV)) -> 
  (DSBOOL x) ~{ sigma }~> sigma'
| ds_char :forall x sigma sigma' , 
   sigma' = (update sigma x (cons_stiva_char (stiva_vida CharV))) -> 
  (DSCHAR x) ~{ sigma }~> sigma'
| e_push_nat : forall sigma sigma' sigma'' stiva1 NUM numestiva,
(acelasi_tip (cons_stiva_nat (stiva_vida NaturalV)) (cons_stiva_nat (stiva1))) = true ->
sigma' = update sigma numestiva ( cons_stiva_nat stiva1 )  ->
sigma'' =( update sigma numestiva (cons_stiva_nat ( Stiva_Push NaturalV stiva1 NUM) ) )->
push_stiva_nat numestiva NUM ~{ sigma' }~> sigma''
| e_push_bool : forall sigma sigma' sigma'' stiva1 NUM numestiva,
(acelasi_tip (cons_stiva_bool (stiva_vida BooleanV)) (cons_stiva_bool (stiva1))) = true ->
sigma' = update sigma numestiva ( cons_stiva_bool stiva1 )  ->
sigma'' =( update sigma numestiva (cons_stiva_bool ( Stiva_Push BooleanV stiva1 NUM) ) )->
push_stiva_bool numestiva NUM ~{ sigma' }~> sigma''
| e_push_char : forall sigma sigma' sigma'' stiva1 NUM numestiva,
(acelasi_tip (cons_stiva_char (stiva_vida CharV)) (cons_stiva_char (stiva1))) = true ->
sigma' = update sigma numestiva ( cons_stiva_char stiva1 )  ->
sigma'' =( update sigma numestiva (cons_stiva_char ( Stiva_Push CharV stiva1 NUM) ) )->
push_stiva_char numestiva NUM ~{ sigma' }~> sigma''
| e_pop_nat : forall sigma sigma' sigma'' stiva1 numestiva,
(acelasi_tip (cons_stiva_nat (stiva_vida NaturalV)) (cons_stiva_nat (stiva1))) = true ->
sigma' = update sigma numestiva ( cons_stiva_nat stiva1 )  ->
sigma'' =( update sigma numestiva (cons_stiva_nat ( Stiva_Pop NaturalV stiva1) ) )->
pop_stiva_nat numestiva ~{ sigma' }~> sigma''
| e_pop_bool : forall sigma sigma' sigma'' stiva1 numestiva,
(acelasi_tip (cons_stiva_bool (stiva_vida BooleanV)) (cons_stiva_bool (stiva1))) = true ->
sigma' = update sigma numestiva ( cons_stiva_bool stiva1 )  ->
sigma'' =( update sigma numestiva (cons_stiva_bool ( Stiva_Pop BooleanV stiva1) ) )->
pop_stiva_bool numestiva ~{ sigma' }~> sigma''
| e_pop_char : forall sigma sigma' sigma'' stiva1 numestiva,
(acelasi_tip (cons_stiva_char (stiva_vida CharV)) (cons_stiva_char (stiva1))) = true ->
sigma' = update sigma numestiva ( cons_stiva_char stiva1 )  ->
sigma'' = update sigma numestiva (cons_stiva_char ( Stiva_Pop CharV stiva1 ) )->
pop_stiva_char numestiva ~{ sigma' }~> sigma'' 
| e_concat_nat : forall stiva1 stiva2 numestiva1 numestiva2 sigma sigma' sigma'' sigma''' ,
(acelasi_tip (cons_stiva_nat (stiva_vida NaturalV)) (cons_stiva_nat (stiva1))) = true ->
(acelasi_tip (cons_stiva_nat (stiva_vida NaturalV)) (cons_stiva_nat (stiva2))) = true ->
sigma' = update sigma numestiva1 ( cons_stiva_nat stiva1 )  ->
sigma'' = update sigma' numestiva2 ( cons_stiva_nat stiva2 )  ->
sigma''' = update sigma'' numestiva1 (cons_stiva_nat (concat_stive NaturalV stiva1 stiva2) ) ->
concat_stive_nat numestiva1 numestiva2 ~{ sigma }~> sigma'''
| e_concat_bool : forall stiva1 stiva2 numestiva1 numestiva2 sigma sigma' sigma'' sigma''' ,
(acelasi_tip (cons_stiva_bool (stiva_vida BooleanV)) (cons_stiva_bool (stiva1))) = true ->
(acelasi_tip (cons_stiva_bool (stiva_vida BooleanV)) (cons_stiva_bool (stiva2))) = true ->
sigma' = update sigma numestiva1 ( cons_stiva_bool stiva1 )  ->
sigma'' = update sigma' numestiva2 ( cons_stiva_bool stiva2 )  ->
sigma''' = update sigma'' numestiva1 (cons_stiva_bool (concat_stive BooleanV stiva1 stiva2) ) ->
concat_stive_nat numestiva1 numestiva2 ~{ sigma }~> sigma'''
| e_concat_char : forall stiva1 stiva2 numestiva1 numestiva2 sigma sigma' sigma'' sigma''' ,
(acelasi_tip (cons_stiva_char (stiva_vida CharV)) (cons_stiva_char (stiva1))) = true ->
(acelasi_tip (cons_stiva_char (stiva_vida CharV)) (cons_stiva_char (stiva2))) = true ->
sigma' = update sigma numestiva1 ( cons_stiva_char stiva1 )  ->
sigma'' = update sigma' numestiva2 ( cons_stiva_char stiva2 )  ->
sigma''' = update sigma'' numestiva1 (cons_stiva_char (strcat stiva1 stiva2) ) ->
strcat' (numestiva1 , numestiva2) ~{ sigma }~> sigma'''
| e_copy_nat : forall stiva1 stiva2 numestiva1 numestiva2 sigma sigma' sigma'' sigma''' ,
(acelasi_tip (cons_stiva_nat (stiva_vida NaturalV)) (cons_stiva_nat (stiva1))) = true ->
(acelasi_tip (cons_stiva_nat (stiva_vida NaturalV)) (cons_stiva_nat (stiva2))) = true ->
sigma' = update sigma numestiva1 ( cons_stiva_nat stiva1 )  ->
sigma'' = update sigma' numestiva2 ( cons_stiva_nat stiva2 )  ->
sigma''' = update sigma'' numestiva1 (cons_stiva_nat (Copie_Stiva NaturalV stiva1 stiva2) ) ->
copy_stive_nat numestiva1 numestiva2 ~{ sigma }~> sigma'''
| e_copy_bool : forall stiva1 stiva2 numestiva1 numestiva2 sigma sigma' sigma'' sigma''' ,
(acelasi_tip (cons_stiva_bool (stiva_vida BooleanV)) (cons_stiva_bool (stiva1))) = true ->
(acelasi_tip (cons_stiva_bool (stiva_vida BooleanV)) (cons_stiva_bool (stiva2))) = true ->
sigma' = update sigma numestiva1 ( cons_stiva_bool stiva1 )  ->
sigma'' = update sigma' numestiva2 ( cons_stiva_bool stiva2 )  ->
sigma''' = update sigma'' numestiva1 (cons_stiva_bool (Copie_Stiva BooleanV stiva1 stiva2) ) ->
copy_stive_nat numestiva1 numestiva2 ~{ sigma }~> sigma'''
| e_copy_char : forall stiva1 stiva2 numestiva1 numestiva2 sigma sigma' sigma'' sigma''' ,
(acelasi_tip (cons_stiva_char (stiva_vida CharV)) (cons_stiva_char (stiva1))) = true ->
(acelasi_tip (cons_stiva_char (stiva_vida CharV)) (cons_stiva_char (stiva2))) = true ->
sigma' = update sigma numestiva1 ( cons_stiva_char stiva1 )  ->
sigma'' = update sigma' numestiva2 ( cons_stiva_char stiva2 )  ->
sigma''' = update sigma'' numestiva1 (cons_stiva_char (strcpy stiva1 stiva2) ) ->
strcpy' (numestiva1 , numestiva2) ~{ sigma }~> sigma'''
| e_decl_struct :forall X S sigma sigma' ,
sigma' = update sigma X (cons_struct S) ->
declare_struct X S ~{ sigma }~> sigma'
| e_update_struct_value :forall nume S sigma sigma'' sigma' val new,
sigma' = update sigma nume (cons_struct S) ->
sigma'' = update sigma' (GetV S val) new -> 
(update_struct_value nume val new) ~{ sigma }~> sigma'' 
where "S ~{ Sigma }~> Sigma'":=(eval S Sigma Sigma') .

Hint Constructors aeval : my_hints.
Hint Constructors beval : my_hints.
Hint Constructors eval : my_hints.
Hint Unfold update : my_hints.
Example prgm1 := 
 DNAT "i"  ;;
 DNAT "j"  ;;
DNAT "sum" ;;
assign_nat "i" 3 ;;
assign_nat "j" 4 ;;
assign_nat "sum" ("i" +' "j"). 
Qed.
Example eval_sum1 :
  exists state, prgm1 ~{ env0 }~> state /\ state "sum" =cons_nat 7.
Proof.
eexists.
split.
unfold prgm1.
eapply e_seq.
eapply d_nat.
reflexivity.
eapply e_seq.
eapply d_nat.
reflexivity.
eapply e_seq.
eapply d_nat.
eauto.
eapply e_seq.
eapply a_nat.
eapply const.
eauto.
eapply e_seq.
eapply a_nat.
eapply const.
eauto.
eapply a_nat.
eapply add.
eapply var.
eapply var.
simpl.
reflexivity.
reflexivity.
reflexivity.
Qed.

Example prgm2 := 
 DNAT "i"  ;;
 DNAT "j"  ;;
DNAT "sum" ;;
assign_nat "i" 4 ;;
assign_nat "j" 4 ;;
while ( "i" <=' "j" )  
(  assign_nat "sum" ("sum" +' 20) ;;
   assign_nat "i" ("i" +' 1)   ).


Example eval_sum2 :
  exists state, prgm2 ~{ env0 }~> state /\ state "sum" =cons_nat 20.
Proof.
eexists.
split.
unfold prgm1.
eapply e_seq.
eapply d_nat.
reflexivity.
eapply e_seq.
eapply d_nat.
reflexivity.
eapply e_seq.
eapply d_nat.
reflexivity.
eapply e_seq.

eapply a_nat.
eapply const.
reflexivity.
eapply e_seq.
eapply a_nat.
eapply const.
reflexivity.
eapply e_whiletrue.
eapply lessthan_b.
eapply var.
eapply var.
simpl.
eauto.
eapply e_seq.
eapply e_seq.
eapply a_nat.
eapply add.
eapply var.
eapply const.
simpl.
reflexivity.
reflexivity.
eapply a_nat.
eapply add.
eapply var.
eapply const.
simpl.
reflexivity.
reflexivity.
eapply e_whilefalse.
eapply lessthan_b.
eapply var.
eapply var.
eauto.
eauto.
Qed.

Definition prgrm3 :=
DSNAT "stiva"  ;;
push_stiva_nat "stiva" 3 ;;
push_stiva_nat "stiva" 6 ;;
pop_stiva_nat "stiva" .

Example eval_sum3 :
  exists state, prgrm3 ~{ env0 }~> state /\ state "stiva" =cons_stiva_nat (stiva_nevida NaturalV 3 (stiva_vida NaturalV)) .
eexists.
split.
unfold prgrm3.
eapply e_seq.
eapply ds_nat.
eauto.
eapply e_seq.
eapply e_push_nat.
eauto.
eauto.
eauto.
eapply e_seq.
eapply e_push_nat.
eauto.
eauto.
eauto.
eauto.
eauto.
eapply e_pop_nat.
eauto.
eauto.
eauto.
eauto.
Qed.

Example prgm4 := 
 DNAT "i"  ;;
 DNAT "j"  ;;
DNAT "sum" ;;
assign_nat "i" 4 ;;
assign_nat "j" 4 ;;
while ( "i" <=' 20 )  
(assign_nat "sum" ("sum" +' 20) ;;
   assign_nat "i" ("i" +' 1) ;; 
   break   ).


Example eval_sum4 :
  exists state, prgm4 ~{ env0 }~> state /\ state "sum" =cons_nat 20.
Proof.
eexists.
split.
unfold prgm4.
eapply e_seq.
eapply d_nat.
eauto.
eapply e_seq.
eapply d_nat.
eauto.
eapply e_seq.
eapply d_nat.
eauto.
eapply e_seq.
eapply a_nat.
eauto.
eapply const.
eauto.
eapply e_seq.
eapply a_nat.
eauto.
eapply const.
eauto.
eapply e_while_break_1.
eapply lessthan_b.
eapply var.
eapply const.
reflexivity.
eapply e_seq.
eapply a_nat.
eapply add.
eapply var.
eapply const.
simpl.
reflexivity.
reflexivity.
eapply e_seq.
eapply a_nat.
eapply add.
eapply var.
eapply const.
simpl.
reflexivity.
reflexivity.
eapply e_break.
reflexivity.
Qed.
