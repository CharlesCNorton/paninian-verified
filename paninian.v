(******************************************************************************)
(*                                                                            *)
(*        Pāṇinian Sandhi: A Verified Formalization of Aṣṭādhyāyī 6.1         *)
(*                                                                            *)
(*   Phoneme inventory (varṇa-samāmnāya) via the 14 Śiva Sūtras, pratyāhāra   *)
(*   sound-class abbreviations, and vowel sandhi (ac-sandhi) rules:           *)
(*                                                                            *)
(*     6.1.77  iko yaṇ aci           (ik → yaṇ before vowels)                 *)
(*     6.1.78  eco 'yavāyāvaḥ        (ec → ay/av/āy/āv before vowels)         *)
(*     6.1.87  ādguṇaḥ               (a/ā + vowel → guṇa)                     *)
(*     6.1.88  vṛddhir eci           (a/ā + guṇa vowel → vṛddhi)              *)
(*     6.1.101 akaḥ savarṇe dīrghaḥ  (similar vowels → long)                  *)
(*                                                                            *)
(*   "vipratiṣedhe paraṁ kāryam."                                             *)
(*   - Pāṇini, Aṣṭādhyāyī 1.4.2                                               *)
(*                                                                            *)
(*   Author: Charles C. Norton                                                *)
(*   Date: December 2025                                                      *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

Set Implicit Arguments.

(** * Phoneme Inventory (varṇa-samāmnāya) *)

(** Vowels (svara) per Śiva Sūtras 1-4: a i u ṇ | ṛ ḷ k | e o ṅ | ai au c.
    Long vowels (ā ī ū ṝ) are savarṇa with their short counterparts. *)

Inductive Vowel : Type :=
  | V_a | V_aa
  | V_i | V_ii
  | V_u | V_uu
  | V_r | V_rr
  | V_l
  | V_e | V_ai
  | V_o | V_au.

(** Consonants (vyañjana) per Śiva Sūtras 5-14.
    Stops (sparśa) in five vargas, semivowels (antaḥstha), sibilants (ūṣman). *)

Inductive Consonant : Type :=
  | C_k | C_kh | C_g | C_gh | C_ng
  | C_c | C_ch | C_j | C_jh | C_ny
  | C_tt | C_tth | C_dd | C_ddh | C_nn
  | C_t | C_th | C_d | C_dh | C_n
  | C_p | C_ph | C_b | C_bh | C_m
  | C_y | C_r | C_l | C_v
  | C_sh | C_ss | C_s
  | C_h.

(** Phoneme: vowel, consonant, anusvāra (ṃ), or visarga (ḥ). *)

Inductive Phoneme : Type :=
  | Svar : Vowel -> Phoneme
  | Vyan : Consonant -> Phoneme
  | Anusvara : Phoneme
  | Visarga : Phoneme.

Definition Word := list Phoneme.

Scheme Equality for Vowel.
Scheme Equality for Consonant.
Scheme Equality for Phoneme.

(** Vowel length. *)

Definition is_long (v : Vowel) : bool :=
  match v with
  | V_aa | V_ii | V_uu | V_rr | V_e | V_ai | V_o | V_au => true
  | _ => false
  end.

Definition is_short (v : Vowel) : bool := negb (is_long v).

(** Savarṇa: vowels with same point of articulation (1.1.9). *)

Inductive SavarnaClass := SC_a | SC_i | SC_u | SC_r | SC_l | SC_e | SC_ai | SC_o | SC_au.

Definition savarna_class (v : Vowel) : SavarnaClass :=
  match v with
  | V_a | V_aa => SC_a
  | V_i | V_ii => SC_i
  | V_u | V_uu => SC_u
  | V_r | V_rr => SC_r
  | V_l => SC_l
  | V_e => SC_e
  | V_ai => SC_ai
  | V_o => SC_o
  | V_au => SC_au
  end.

Scheme Equality for SavarnaClass.

Definition savarna (v1 v2 : Vowel) : bool :=
  SavarnaClass_beq (savarna_class v1) (savarna_class v2).

(** Guṇa grade (1.1.2): a, e, o, ar, al. *)

Definition guna (v : Vowel) : list Phoneme :=
  match v with
  | V_a | V_aa => [Svar V_a]
  | V_i | V_ii => [Svar V_e]
  | V_u | V_uu => [Svar V_o]
  | V_r | V_rr => [Svar V_a; Vyan C_r]
  | V_l => [Svar V_a; Vyan C_l]
  | V_e => [Svar V_e]
  | V_o => [Svar V_o]
  | V_ai => [Svar V_ai]
  | V_au => [Svar V_au]
  end.

(** Vṛddhi grade (1.1.1): ā, ai, au, ār, āl. *)

Definition vrddhi (v : Vowel) : list Phoneme :=
  match v with
  | V_a | V_aa => [Svar V_aa]
  | V_i | V_ii => [Svar V_ai]
  | V_u | V_uu => [Svar V_au]
  | V_r | V_rr => [Svar V_aa; Vyan C_r]
  | V_l => [Svar V_aa; Vyan C_l]
  | V_e => [Svar V_ai]
  | V_o => [Svar V_au]
  | V_ai => [Svar V_ai]
  | V_au => [Svar V_au]
  end.

(** Is this vowel already at guṇa grade? (e, o are guṇa of i, u). *)

Definition is_guna (v : Vowel) : bool :=
  match v with
  | V_e | V_o => true
  | _ => false
  end.

(** Lengthen a simple vowel (for 6.1.101). *)

Definition lengthen (v : Vowel) : Vowel :=
  match v with
  | V_a => V_aa
  | V_i => V_ii
  | V_u => V_uu
  | V_r => V_rr
  | other => other
  end.

(** ik vowels: i ī u ū ṛ ṝ ḷ (pratyāhāra from Śiva Sūtra 1-2). *)

Definition is_ik (v : Vowel) : bool :=
  match v with
  | V_i | V_ii | V_u | V_uu | V_r | V_rr | V_l => true
  | _ => false
  end.

(** yaṇ: corresponding semivowels y r l v (for 6.1.77). *)

Definition yan_of (v : Vowel) : option Consonant :=
  match v with
  | V_i | V_ii => Some C_y
  | V_u | V_uu => Some C_v
  | V_r | V_rr => Some C_r
  | V_l => Some C_l
  | _ => None
  end.

(** ec vowels: e o ai au (pratyāhāra from Śiva Sūtra 3-4). *)

Definition is_ec (v : Vowel) : bool :=
  match v with
  | V_e | V_o | V_ai | V_au => true
  | _ => false
  end.

(** ayavāyāv: e→ay, o→av, ai→āy, au→āv (for 6.1.78). *)

Definition ayavayav (v : Vowel) : option (list Phoneme) :=
  match v with
  | V_e => Some [Svar V_a; Vyan C_y]
  | V_o => Some [Svar V_a; Vyan C_v]
  | V_ai => Some [Svar V_aa; Vyan C_y]
  | V_au => Some [Svar V_aa; Vyan C_v]
  | _ => None
  end.

(** * Pratyāhāra (Sound Classes) *)

(** ac: all vowels (Śiva Sūtra 1-4, from a to anubandha c). *)

Definition is_ac (v : Vowel) : bool := true.

(** ak: simple vowels a ā i ī u ū ṛ ṝ ḷ (Śiva Sūtra 1-2, to anubandha k). *)

Definition is_ak (v : Vowel) : bool :=
  match v with
  | V_a | V_aa | V_i | V_ii | V_u | V_uu | V_r | V_rr | V_l => true
  | _ => false
  end.

(** hal: all consonants (Śiva Sūtra 5-14, from h to anubandha l). *)

Definition is_hal (c : Consonant) : bool := true.

(** * Sūtra Representation *)

(** Sūtra number: adhyāya (1-8), pāda (1-4), sūtra number. *)

Record SutraNum := {
  adhyaya : nat;
  pada : nat;
  sutra : nat
}.

(** Lexicographic ordering on sūtra numbers (for para precedence). *)

Definition sutra_ltb (s1 s2 : SutraNum) : bool :=
  if Nat.ltb (adhyaya s1) (adhyaya s2) then true
  else if Nat.eqb (adhyaya s1) (adhyaya s2) then
    if Nat.ltb (pada s1) (pada s2) then true
    else if Nat.eqb (pada s1) (pada s2) then
      Nat.ltb (sutra s1) (sutra s2)
    else false
  else false.

Definition sutra_leb (s1 s2 : SutraNum) : bool :=
  sutra_ltb s1 s2 || (Nat.eqb (adhyaya s1) (adhyaya s2) &&
                      Nat.eqb (pada s1) (pada s2) &&
                      Nat.eqb (sutra s1) (sutra s2)).

(** A vowel sandhi rule: applies at vowel+vowel boundary. *)

Record AcSandhiRule := {
  rule_num : SutraNum;
  rule_apavada_of : option SutraNum;
  rule_condition : Vowel -> Vowel -> bool;
  apply_rule : Vowel -> Vowel -> list Phoneme
}.

Definition rule_matches (r : AcSandhiRule) (v1 v2 : Vowel) : bool :=
  rule_condition r v1 v2.

(** * Precedence (vipratiṣedhe paraṁ kāryam) *)

(** Check if r1 is an apavāda (exception) to r2. *)

Definition is_apavada_of (r1 r2 : AcSandhiRule) : bool :=
  match rule_apavada_of r1 with
  | Some sn => Nat.eqb (adhyaya sn) (adhyaya (rule_num r2)) &&
               Nat.eqb (pada sn) (pada (rule_num r2)) &&
               Nat.eqb (sutra sn) (sutra (rule_num r2))
  | None => false
  end.

(** Rule r1 defeats r2 if: r1 is apavāda of r2, or (neither is apavāda
    of the other and r1 comes later per para). *)

Definition rule_defeats (r1 r2 : AcSandhiRule) : bool :=
  is_apavada_of r1 r2 ||
  (negb (is_apavada_of r2 r1) && sutra_ltb (rule_num r2) (rule_num r1)).

(** Select winning rule from two conflicting rules. *)

Definition prefer_rule (r1 r2 : AcSandhiRule) : AcSandhiRule :=
  if rule_defeats r1 r2 then r1 else r2.

(** Find best matching rule from a list. *)

Fixpoint best_rule_rec (rules : list AcSandhiRule) (v1 v2 : Vowel)
    (acc : option AcSandhiRule) : option AcSandhiRule :=
  match rules with
  | [] => acc
  | r :: rs =>
      let acc' :=
        if rule_matches r v1 v2 then
          match acc with
          | None => Some r
          | Some best => Some (prefer_rule r best)
          end
        else acc
      in best_rule_rec rs v1 v2 acc'
  end.

Definition best_rule (rules : list AcSandhiRule) (v1 v2 : Vowel)
  : option AcSandhiRule :=
  best_rule_rec rules v1 v2 None.

(** * Vowel Sandhi Rules (ac-sandhi, adhyāya 6 pāda 1) *)

(** 6.1.101 akaḥ savarṇe dīrghaḥ: ak vowel + savarṇa → long vowel.
    Apavāda of 6.1.87. *)

Definition rule_6_1_101 : AcSandhiRule := {|
  rule_num := {| adhyaya := 6; pada := 1; sutra := 101 |};
  rule_apavada_of := Some {| adhyaya := 6; pada := 1; sutra := 87 |};
  rule_condition := fun v1 v2 => is_ak v1 && is_ak v2 && savarna v1 v2;
  apply_rule := fun v1 v2 => [Svar (lengthen v1)]
|}.

(** 6.1.77 iko yaṇ aci: ik vowel + any vowel → semivowel + vowel. *)

Definition apply_6_1_77 (v1 v2 : Vowel) : list Phoneme :=
  match yan_of v1 with
  | Some c => [Vyan c; Svar v2]
  | None => []
  end.

Definition rule_6_1_77 : AcSandhiRule := {|
  rule_num := {| adhyaya := 6; pada := 1; sutra := 77 |};
  rule_apavada_of := None;
  rule_condition := fun v1 v2 => is_ik v1 && negb (savarna v1 v2);
  apply_rule := apply_6_1_77
|}.

(** 6.1.78 eco 'yavāyāvaḥ: ec vowel + vowel → ay/av/āy/āv + vowel. *)

Definition apply_6_1_78 (v1 v2 : Vowel) : list Phoneme :=
  match ayavayav v1 with
  | Some prefix => prefix ++ [Svar v2]
  | None => []
  end.

Definition rule_6_1_78 : AcSandhiRule := {|
  rule_num := {| adhyaya := 6; pada := 1; sutra := 78 |};
  rule_apavada_of := None;
  rule_condition := fun v1 v2 => is_ec v1;
  apply_rule := apply_6_1_78
|}.

(** 6.1.87 ādguṇaḥ: a/ā + vowel → guṇa (replaces both). *)

Definition is_a_class (v : Vowel) : bool :=
  match v with V_a | V_aa => true | _ => false end.

Definition rule_6_1_87 : AcSandhiRule := {|
  rule_num := {| adhyaya := 6; pada := 1; sutra := 87 |};
  rule_apavada_of := None;
  rule_condition := fun v1 v2 => is_a_class v1 && negb (is_a_class v2);
  apply_rule := fun _ v2 => guna v2
|}.

(** 6.1.88 vṛddhir eci: a/ā + ec vowel → vṛddhi.
    Apavāda of 6.1.87. *)

Definition rule_6_1_88 : AcSandhiRule := {|
  rule_num := {| adhyaya := 6; pada := 1; sutra := 88 |};
  rule_apavada_of := Some {| adhyaya := 6; pada := 1; sutra := 87 |};
  rule_condition := fun v1 v2 => is_a_class v1 && is_ec v2;
  apply_rule := fun _ v2 => vrddhi v2
|}.

(** All ac-sandhi rules from 6.1. *)

Definition ac_sandhi_rules : list AcSandhiRule :=
  [rule_6_1_77; rule_6_1_78; rule_6_1_87; rule_6_1_88; rule_6_1_101].

(** Apply sandhi at a vowel-vowel boundary. *)

Definition apply_ac_sandhi (v1 v2 : Vowel) : list Phoneme :=
  match best_rule ac_sandhi_rules v1 v2 with
  | Some r => apply_rule r v1 v2
  | None => [Svar v1; Svar v2]
  end.

(** * Examples *)

(** a + a → ā (6.1.101). *)
Example ex_aa : apply_ac_sandhi V_a V_a = [Svar V_aa].
Proof. reflexivity. Qed.

(** a + i → e (6.1.87 guṇa). *)
Example ex_ai : apply_ac_sandhi V_a V_i = [Svar V_e].
Proof. reflexivity. Qed.

(** a + u → o (6.1.87 guṇa). *)
Example ex_au : apply_ac_sandhi V_a V_u = [Svar V_o].
Proof. reflexivity. Qed.

(** a + e → ai (6.1.88 vṛddhi). *)
Example ex_ae : apply_ac_sandhi V_a V_e = [Svar V_ai].
Proof. reflexivity. Qed.

(** i + a → ya (6.1.77). *)
Example ex_ia : apply_ac_sandhi V_i V_a = [Vyan C_y; Svar V_a].
Proof. reflexivity. Qed.

(** u + a → va (6.1.77). *)
Example ex_ua : apply_ac_sandhi V_u V_a = [Vyan C_v; Svar V_a].
Proof. reflexivity. Qed.

(** e + a → aya (6.1.78). *)
Example ex_ea : apply_ac_sandhi V_e V_a = [Svar V_a; Vyan C_y; Svar V_a].
Proof. reflexivity. Qed.

(** * Metatheory *)

(** best_rule is deterministic: same inputs yield same output. *)

Lemma best_rule_deterministic : forall rules v1 v2 r1 r2,
  best_rule rules v1 v2 = Some r1 ->
  best_rule rules v1 v2 = Some r2 ->
  r1 = r2.
Proof.
  intros rules v1 v2 r1 r2 H1 H2.
  rewrite H1 in H2.
  injection H2.
  auto.
Qed.

(** apply_ac_sandhi is a total function. *)

Lemma apply_ac_sandhi_total : forall v1 v2,
  exists result, apply_ac_sandhi v1 v2 = result.
Proof.
  intros v1 v2.
  eexists.
  reflexivity.
Qed.

(** apply_ac_sandhi is deterministic. *)

Lemma apply_ac_sandhi_deterministic : forall v1 v2 r1 r2,
  apply_ac_sandhi v1 v2 = r1 ->
  apply_ac_sandhi v1 v2 = r2 ->
  r1 = r2.
Proof.
  intros v1 v2 r1 r2 H1 H2.
  congruence.
Qed.

(** Rule 6.1.101 (apavāda) defeats 6.1.87 (utsarga) when both match. *)

Lemma apavada_defeats_utsarga :
  is_apavada_of rule_6_1_101 rule_6_1_87 = true.
Proof. reflexivity. Qed.

Lemma rule_6_1_101_defeats_6_1_87 :
  rule_defeats rule_6_1_101 rule_6_1_87 = true.
Proof. reflexivity. Qed.

(** 6.1.88 is apavāda of 6.1.87. *)

Lemma apavada_6_1_88_of_6_1_87 :
  is_apavada_of rule_6_1_88 rule_6_1_87 = true.
Proof. reflexivity. Qed.

(** Coverage: every vowel pair triggers some rule. *)

Lemma ac_sandhi_coverage : forall v1 v2,
  exists r, best_rule ac_sandhi_rules v1 v2 = Some r.
Proof.
  intros v1 v2.
  unfold ac_sandhi_rules, best_rule.
  destruct v1, v2; cbn; eexists; reflexivity.
Qed.

(** The sandhi output is never empty. *)

Lemma apply_ac_sandhi_nonempty : forall v1 v2,
  apply_ac_sandhi v1 v2 <> [].
Proof.
  intros v1 v2.
  unfold apply_ac_sandhi, ac_sandhi_rules, best_rule.
  destruct v1, v2; cbn; intro H; discriminate H.
Qed.
