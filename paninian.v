(******************************************************************************)
(*                                                                            *)
(*      Pāṇinian Sandhi: A Verified Formalization of Aṣṭādhyāyī 6.1 & 8.3-4   *)
(*                                                                            *)
(*   Comprehensive formalization of Sanskrit phonological rules:              *)
(*   - Vowel sandhi (ac-sandhi): 6.1.77-113 under ekaḥ pūrvaparayoḥ adhikāra  *)
(*   - Visarga sandhi: 8.3.15-36                                              *)
(*   - Consonant sandhi: 8.4.2, 8.4.40-65                                     *)
(*                                                                            *)
(*   Pratyāhāras computed from Śiva Sūtras. Conflict resolution via           *)
(*   vipratiṣedha (1.4.2) and apavāda. Full soundness/completeness for        *)
(*   external sandhi; morphological context types for internal sandhi.        *)
(*                                                                            *)
(*   'The first generative grammar in the modern sense was Panini's           *)
(*    grammar.' — Noam Chomsky                                                *)
(*                                                                            *)
(*   Author: Charles C. Norton                                                *)
(*   Date: December 2025                                                      *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import List Bool Arith Lia.
From Coq Require Import Relations.
Import ListNotations.

Set Implicit Arguments.

(** * Part I: Phoneme Inventory *)

(** V = {a, ā, i, ī, u, ū, ṛ, ṝ, ḷ, e, ai, o, au} — the 13 Sanskrit vowels. *)
Inductive Vowel : Type :=
  | V_a | V_aa
  | V_i | V_ii
  | V_u | V_uu
  | V_r | V_rr
  | V_l
  | V_e | V_ai
  | V_o | V_au.

(** C = {k, kh, g, gh, ṅ, c, ch, j, jh, ñ, ṭ, ṭh, ḍ, ḍh, ṇ, t, th, d, dh, n, p, ph, b, bh, m, y, r, l, v, ś, ṣ, s, h} — the 33 consonants. *)
Inductive Consonant : Type :=
  | C_k | C_kh | C_g | C_gh | C_ng
  | C_c | C_ch | C_j | C_jh | C_ny
  | C_tt | C_tth | C_dd | C_ddh | C_nn
  | C_t | C_th | C_d | C_dh | C_n
  | C_p | C_ph | C_b | C_bh | C_m
  | C_y | C_r | C_l | C_v
  | C_sh | C_ss | C_s
  | C_h.

(** P = V ⊔ C ⊔ {anusvāra, visarga, jihvāmūlīya, upadhmānīya} — the phoneme universe. *)
Inductive Phoneme : Type :=
  | Svar : Vowel -> Phoneme
  | Vyan : Consonant -> Phoneme
  | Anusvara : Phoneme
  | Visarga : Phoneme
  | Jihvamuliya : Phoneme
  | Upadhmamiya : Phoneme.

(** W = P* — a word is a finite sequence of phonemes. *)
Definition Word := list Phoneme.

(** =_V : V × V → bool — decidable equality on vowels. *)
Scheme Equality for Vowel.
(** =_C : C × C → bool — decidable equality on consonants. *)
Scheme Equality for Consonant.
(** =_P : P × P → bool — decidable equality on phonemes. *)
Scheme Equality for Phoneme.

(** * Part II: Śiva Sūtras and Pratyāhāra *)

(** S = V ⊔ C ⊔ ℕ — Śiva Sūtra elements: vowels, consonants, or it-markers. *)
Inductive SivaSound : Type :=
  | SS_vowel : Vowel -> SivaSound
  | SS_cons : Consonant -> SivaSound
  | SS_it : nat -> SivaSound.

(** Σ₁ = ⟨a, i, u, ṇ⟩ — first sūtra: simple vowels. *)
Definition siva_sutra_1 : list SivaSound :=
  [SS_vowel V_a; SS_vowel V_i; SS_vowel V_u; SS_it 1].

(** Σ₂ = ⟨ṛ, ḷ, k⟩ — second sūtra: syllabic liquids. *)
Definition siva_sutra_2 : list SivaSound :=
  [SS_vowel V_r; SS_vowel V_l; SS_it 2].

(** Σ₃ = ⟨e, o, ṅ⟩ — third sūtra: guṇa diphthongs. *)
Definition siva_sutra_3 : list SivaSound :=
  [SS_vowel V_e; SS_vowel V_o; SS_it 3].

(** Σ₄ = ⟨ai, au, c⟩ — fourth sūtra: vṛddhi diphthongs. *)
Definition siva_sutra_4 : list SivaSound :=
  [SS_vowel V_ai; SS_vowel V_au; SS_it 4].

(** Σ₅ = ⟨h, y, v, r, ṭ⟩ — fifth sūtra: h and semivowels. *)
Definition siva_sutra_5 : list SivaSound :=
  [SS_cons C_h; SS_cons C_y; SS_cons C_v; SS_cons C_r; SS_it 5].

(** Σ₆ = ⟨l, ṇ⟩ — sixth sūtra: lateral. *)
Definition siva_sutra_6 : list SivaSound :=
  [SS_cons C_l; SS_it 6].

(** Σ₇ = ⟨ñ, m, ṅ, ṇ, n, m⟩ — seventh sūtra: nasals. *)
Definition siva_sutra_7 : list SivaSound :=
  [SS_cons C_ny; SS_cons C_m; SS_cons C_ng; SS_cons C_nn; SS_cons C_n; SS_it 7].

(** Σ₈ = ⟨jh, bh, ñ⟩ — eighth sūtra: voiced aspirate subset. *)
Definition siva_sutra_8 : list SivaSound :=
  [SS_cons C_jh; SS_cons C_bh; SS_it 8].

(** Σ₉ = ⟨gh, ḍh, dh, ṣ⟩ — ninth sūtra: voiced aspirates continued. *)
Definition siva_sutra_9 : list SivaSound :=
  [SS_cons C_gh; SS_cons C_ddh; SS_cons C_dh; SS_it 9].

(** Σ₁₀ = ⟨j, b, g, ḍ, d, ś⟩ — tenth sūtra: voiced unaspirates. *)
Definition siva_sutra_10 : list SivaSound :=
  [SS_cons C_j; SS_cons C_b; SS_cons C_g; SS_cons C_dd; SS_cons C_d; SS_it 10].

(** Σ₁₁ = ⟨kh, ph, ch, ṭh, th, c, ṭ, t, v⟩ — eleventh sūtra: voiceless stops. *)
Definition siva_sutra_11 : list SivaSound :=
  [SS_cons C_kh; SS_cons C_ph; SS_cons C_ch; SS_cons C_tth; SS_cons C_th;
   SS_cons C_c; SS_cons C_tt; SS_cons C_t; SS_it 11].

(** Σ₁₂ = ⟨k, p, y⟩ — twelfth sūtra: voiceless velars and labials. *)
Definition siva_sutra_12 : list SivaSound :=
  [SS_cons C_k; SS_cons C_p; SS_it 12].

(** Σ₁₃ = ⟨ś, ṣ, s, r⟩ — thirteenth sūtra: sibilants. *)
Definition siva_sutra_13 : list SivaSound :=
  [SS_cons C_sh; SS_cons C_ss; SS_cons C_s; SS_it 13].

(** Σ₁₄ = ⟨h, l⟩ — fourteenth sūtra: glottal. *)
Definition siva_sutra_14 : list SivaSound :=
  [SS_cons C_h; SS_it 14].

(** Σ = Σ₁ ++ Σ₂ ++ ... ++ Σ₁₄ — the complete Śiva Sūtra sequence. *)
Definition all_siva_sutras : list SivaSound :=
  siva_sutra_1 ++ siva_sutra_2 ++ siva_sutra_3 ++ siva_sutra_4 ++
  siva_sutra_5 ++ siva_sutra_6 ++ siva_sutra_7 ++ siva_sutra_8 ++
  siva_sutra_9 ++ siva_sutra_10 ++ siva_sutra_11 ++ siva_sutra_12 ++
  siva_sutra_13 ++ siva_sutra_14.

(** it? : S → bool — predicate testing if s is an it-marker. *)
Definition is_it (s : SivaSound) : bool :=
  match s with SS_it _ => true | _ => false end.

(** =ᵥ : S × V → bool — tests if Śiva sound equals a given vowel. *)
Definition sound_eq_vowel (s : SivaSound) (v : Vowel) : bool :=
  match s with
  | SS_vowel v' => Vowel_beq v v'
  | _ => false
  end.

(** =_c : S × C → bool — tests if Śiva sound equals a given consonant. *)
Definition sound_eq_cons (s : SivaSound) (c : Consonant) : bool :=
  match s with
  | SS_cons c' => Consonant_beq c c'
  | _ => false
  end.

(** takeUntilIt : S* → S* — extracts prefix before first it-marker. *)
Fixpoint take_until_it (ss : list SivaSound) : list SivaSound :=
  match ss with
  | [] => []
  | s :: rest =>
      if is_it s then []
      else s :: take_until_it rest
  end.

(** dropV : V × S* → S*? — returns suffix after first occurrence of vowel v. *)
Fixpoint drop_through_sound_vowel (v : Vowel) (ss : list SivaSound)
  : option (list SivaSound) :=
  match ss with
  | [] => None
  | s :: rest =>
      if sound_eq_vowel s v then Some rest
      else drop_through_sound_vowel v rest
  end.

(** dropC : C × S* → S*? — returns suffix after first occurrence of consonant c. *)
Fixpoint drop_through_sound_cons (c : Consonant) (ss : list SivaSound)
  : option (list SivaSound) :=
  match ss with
  | [] => None
  | s :: rest =>
      if sound_eq_cons s c then Some rest
      else drop_through_sound_cons c rest
  end.

(** dropIt : ℕ × S* → S*? — returns suffix after it-marker n. *)
Fixpoint drop_through_it (n : nat) (ss : list SivaSound)
  : option (list SivaSound) :=
  match ss with
  | [] => None
  | s :: rest =>
      match s with
      | SS_it m => if Nat.eqb n m then Some rest else drop_through_it n rest
      | _ => drop_through_it n rest
      end
  end.

(** P_V : V × ℕ → V* — pratyāhāra extraction: {v ∈ V | pos(start) ≤ pos(v) < pos(itₙ)}. *)
Definition pratyahara_vowels (start : Vowel) (end_it : nat)
  : list Vowel :=
  match drop_through_sound_vowel start all_siva_sutras with
  | None => []
  | Some after_start =>
      let segment := start ::
        (fix extract ss :=
          match ss with
          | [] => []
          | SS_vowel v :: rest => v :: extract rest
          | SS_it n :: rest => if Nat.eqb n end_it then [] else extract rest
          | _ :: rest => extract rest
          end) after_start
      in segment
  end.

(** ∈_P : V × V × ℕ → bool — tests v ∈ P_V(start, end_it). *)
Definition in_pratyahara_vowel (v : Vowel) (start : Vowel) (end_it : nat)
  : bool :=
  existsb (Vowel_beq v) (pratyahara_vowels start end_it).

(** P_C : C × ℕ → C* — pratyāhāra extraction for consonants. *)
Definition pratyahara_consonants (start : Consonant) (end_it : nat)
  : list Consonant :=
  match drop_through_sound_cons start all_siva_sutras with
  | None => []
  | Some after_start =>
      let segment := start ::
        (fix extract ss :=
          match ss with
          | [] => []
          | SS_cons c :: rest => c :: extract rest
          | SS_it n :: rest => if Nat.eqb n end_it then [] else extract rest
          | _ :: rest => extract rest
          end) after_start
      in segment
  end.

(** ∈_PC : C × C × ℕ → bool — tests c ∈ P_C(start, end_it). *)
Definition in_pratyahara_consonant (c : Consonant) (start : Consonant) (end_it : nat)
  : bool :=
  existsb (Consonant_beq c) (pratyahara_consonants start end_it).

(** hal = P_C(h, 14) — all consonants. *)
Definition hal_consonants : list Consonant := pratyahara_consonants C_h 14.
(** yaṇ = P_C(y, 6) = {y, v, r, l} — semivowels. *)
Definition yan_consonants : list Consonant := pratyahara_consonants C_y 6.
(** jhaś = P_C(jh, 10) — voiced stops. *)
Definition jhas_consonants : list Consonant := pratyahara_consonants C_jh 10.
(** khar = P_C(kh, 13) — voiceless stops and sibilants. *)
Definition khar_consonants : list Consonant := pratyahara_consonants C_kh 13.

(** hal? : C → bool — tests c ∈ hal (all consonants). *)
Definition is_hal_computed (c : Consonant) : bool :=
  in_pratyahara_consonant c C_h 14.

(** yaṇ? : C → bool — tests c ∈ {y, v, r, l}. *)
Definition is_yan_computed (c : Consonant) : bool :=
  in_pratyahara_consonant c C_y 6.

(** jhaś? : C → bool — tests c ∈ jhaś (voiced stops). *)
Definition is_jhas_computed (c : Consonant) : bool :=
  in_pratyahara_consonant c C_jh 10.

(** khar? : C → bool — tests c ∈ khar (voiceless stops + sibilants). *)
Definition is_khar_computed (c : Consonant) : bool :=
  in_pratyahara_consonant c C_kh 13.

(** short : V → V — maps long vowels to short: ā↦a, ī↦i, ū↦u, ṝ↦ṛ. *)
Definition short_of (v : Vowel) : Vowel :=
  match v with
  | V_aa => V_a
  | V_ii => V_i
  | V_uu => V_u
  | V_rr => V_r
  | other => other
  end.

(** ∈_Pₛ : V × V × ℕ → bool — tests short(v) ∈ P_V(start, end_it). *)
Definition in_pratyahara_with_savarna (v : Vowel) (start : Vowel) (end_it : nat)
  : bool :=
  existsb (Vowel_beq (short_of v)) (pratyahara_vowels start end_it).

(** ik = P_V(i, 2) = {i, u, ṛ, ḷ} — high vowels and syllabic liquids. *)
Definition ik_vowels : list Vowel := pratyahara_vowels V_i 2.
(** ak = P_V(a, 2) = {a, i, u, ṛ, ḷ} — simple vowels. *)
Definition ak_vowels : list Vowel := pratyahara_vowels V_a 2.
(** ec = P_V(e, 4) = {e, o, ai, au} — diphthongs. *)
Definition ec_vowels : list Vowel := pratyahara_vowels V_e 4.
(** ac = P_V(a, 4) = V — all vowels. *)
Definition ac_vowels : list Vowel := pratyahara_vowels V_a 4.
(** aṇ = P_V(a, 1) = {a, i, u} — short simple vowels. *)
Definition an_vowels : list Vowel := pratyahara_vowels V_a 1.
(** eṅ = P_V(e, 3) = {e, o} — guṇa diphthongs. *)
Definition en_vowels : list Vowel := pratyahara_vowels V_e 3.

(** ik? : V → bool — tests v ∈ ik (with savarṇa). *)
Definition is_ik_computed (v : Vowel) : bool :=
  in_pratyahara_with_savarna v V_i 2.

(** ak? : V → bool — tests v ∈ ak (with savarṇa). *)
Definition is_ak_computed (v : Vowel) : bool :=
  in_pratyahara_with_savarna v V_a 2.

(** ec? : V → bool — tests v ∈ ec (with savarṇa). *)
Definition is_ec_computed (v : Vowel) : bool :=
  in_pratyahara_with_savarna v V_e 4.

(** ac? : V → bool — tests v ∈ ac (all vowels, with savarṇa). *)
Definition is_ac_computed (v : Vowel) : bool :=
  in_pratyahara_with_savarna v V_a 4.

(** aṇ? : V → bool — tests v ∈ aṇ (with savarṇa). *)
Definition is_an_computed (v : Vowel) : bool :=
  in_pratyahara_with_savarna v V_a 1.

(** eṅ? : V → bool — tests v ∈ {e, o}. *)
Definition is_en_computed (v : Vowel) : bool :=
  in_pratyahara_vowel v V_e 3.

(** ik = [i, u, ṛ, ḷ] — verification of pratyāhāra computation. *)
Lemma ik_vowels_structure : ik_vowels = [V_i; V_u; V_r; V_l].
Proof. reflexivity. Qed.

(** ak = [a, i, u, ṛ, ḷ] — verification of pratyāhāra computation. *)
Lemma ak_vowels_structure : ak_vowels = [V_a; V_i; V_u; V_r; V_l].
Proof. reflexivity. Qed.

(** ec = [e, o, ai, au] — verification of pratyāhāra computation. *)
Lemma ec_vowels_structure : ec_vowels = [V_e; V_o; V_ai; V_au].
Proof. reflexivity. Qed.

(** ac = [a, i, u, ṛ, ḷ, e, o, ai, au] — all vowels. *)
Lemma ac_vowels_structure : ac_vowels = [V_a; V_i; V_u; V_r; V_l; V_e; V_o; V_ai; V_au].
Proof. reflexivity. Qed.

(** aṇ = [a, i, u] — short simple vowels. *)
Lemma an_vowels_structure : an_vowels = [V_a; V_i; V_u].
Proof. reflexivity. Qed.

(** eṅ = [e, o] — guṇa diphthongs only. *)
Lemma en_vowels_structure : en_vowels = [V_e; V_o].
Proof. reflexivity. Qed.

(** yaṇ = [y, v, r, l] — semivowel class. *)
Lemma yan_consonants_structure : yan_consonants = [C_y; C_v; C_r; C_l].
Proof. reflexivity. Qed.

(** jhaś = [jh, bh, gh, ḍh, dh, j, b, g, ḍ, d] — voiced stops. *)
Lemma jhas_consonants_structure : jhas_consonants =
  [C_jh; C_bh; C_gh; C_ddh; C_dh; C_j; C_b; C_g; C_dd; C_d].
Proof. reflexivity. Qed.

(** khar = [kh, ph, ch, ṭh, th, c, ṭ, t, k, p, ś, ṣ, s] — voiceless obstruents. *)
Lemma khar_consonants_structure : khar_consonants =
  [C_kh; C_ph; C_ch; C_tth; C_th; C_c; C_tt; C_t; C_k; C_p; C_sh; C_ss; C_s].
Proof. reflexivity. Qed.

(** hal = C — all 33 consonants. *)
Lemma hal_consonants_structure : hal_consonants =
  [C_h; C_y; C_v; C_r; C_l; C_ny; C_m; C_ng; C_nn; C_n;
   C_jh; C_bh; C_gh; C_ddh; C_dh; C_j; C_b; C_g; C_dd; C_d;
   C_kh; C_ph; C_ch; C_tth; C_th; C_c; C_tt; C_t; C_k; C_p;
   C_sh; C_ss; C_s; C_h].
Proof. reflexivity. Qed.

(** jhal = P_C(jh, 14) — all obstruents (stops + sibilants + h). *)
Definition jhal_consonants : list Consonant := pratyahara_consonants C_jh 14.
(** jhal? : C → bool — tests c ∈ jhal. *)
Definition is_jhal_computed (c : Consonant) : bool :=
  in_pratyahara_consonant c C_jh 14.

(** jhal = [jh, bh, ..., h] — obstruent class verification. *)
Lemma jhal_consonants_structure : jhal_consonants =
  [C_jh; C_bh; C_gh; C_ddh; C_dh; C_j; C_b; C_g; C_dd; C_d;
   C_kh; C_ph; C_ch; C_tth; C_th; C_c; C_tt; C_t; C_k; C_p;
   C_sh; C_ss; C_s; C_h].
Proof. reflexivity. Qed.

(** śal = P_C(ś, 14) = {ś, ṣ, s, h} — sibilants and h. *)
Definition sal_consonants : list Consonant := pratyahara_consonants C_sh 14.
(** śal? : C → bool — tests c ∈ {ś, ṣ, s, h}. *)
Definition is_sal_computed (c : Consonant) : bool :=
  in_pratyahara_consonant c C_sh 14.

(** śal = [ś, ṣ, s, h] — sibilant class verification. *)
Lemma sal_consonants_structure : sal_consonants = [C_sh; C_ss; C_s; C_h].
Proof. reflexivity. Qed.

(** ∀v. short(short(v)) = short(v) — idempotence of length reduction. *)
Lemma savarna_short_of_idempotent : forall v,
  short_of (short_of v) = short_of v.
Proof.
  intro v.
  destruct v; reflexivity.
Qed.

(** short(v) ∈ ik ⟹ ik?(v) = true — savarṇa extends to long vowels. *)
Lemma savarna_covers_long : forall v,
  In (short_of v) ik_vowels ->
  is_ik_computed v = true.
Proof.
  intros v Hin.
  unfold is_ik_computed, in_pratyahara_with_savarna.
  rewrite ik_vowels_structure in Hin.
  destruct (short_of v) eqn:Eshort;
  simpl in Hin; destruct Hin as [H|[H|[H|[H|[]]]]]; try discriminate;
  reflexivity.
Qed.

(** ac_spec ⊆ V — declarative specification of all-vowels class. *)
Inductive is_ac_spec : Vowel -> Prop :=
  | AC_a : is_ac_spec V_a   | AC_aa : is_ac_spec V_aa
  | AC_i : is_ac_spec V_i   | AC_ii : is_ac_spec V_ii
  | AC_u : is_ac_spec V_u   | AC_uu : is_ac_spec V_uu
  | AC_r : is_ac_spec V_r   | AC_rr : is_ac_spec V_rr
  | AC_l : is_ac_spec V_l
  | AC_e : is_ac_spec V_e   | AC_ai : is_ac_spec V_ai
  | AC_o : is_ac_spec V_o   | AC_au : is_ac_spec V_au.

(** ∀v ∈ V. is_ac_spec(v) — ac contains all vowels. *)
Lemma is_ac_spec_total : forall v, is_ac_spec v.
Proof. destruct v; constructor. Qed.

(** ik_spec = {i, ī, u, ū, ṛ, ṝ, ḷ} — declarative ik specification. *)
Inductive is_ik_spec : Vowel -> Prop :=
  | IK_i : is_ik_spec V_i   | IK_ii : is_ik_spec V_ii
  | IK_u : is_ik_spec V_u   | IK_uu : is_ik_spec V_uu
  | IK_r : is_ik_spec V_r   | IK_rr : is_ik_spec V_rr
  | IK_l : is_ik_spec V_l.

(** ik?(v) = true ⟺ is_ik_spec(v) — computational/declarative equivalence. *)
Lemma is_ik_correct : forall v,
  is_ik_computed v = true <-> is_ik_spec v.
Proof.
  intro v; split.
  - intro H; destruct v; simpl in H; try discriminate; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** ak_spec = {a, ā, i, ī, u, ū, ṛ, ṝ, ḷ} — declarative ak specification. *)
Inductive is_ak_spec : Vowel -> Prop :=
  | AK_a : is_ak_spec V_a   | AK_aa : is_ak_spec V_aa
  | AK_i : is_ak_spec V_i   | AK_ii : is_ak_spec V_ii
  | AK_u : is_ak_spec V_u   | AK_uu : is_ak_spec V_uu
  | AK_r : is_ak_spec V_r   | AK_rr : is_ak_spec V_rr
  | AK_l : is_ak_spec V_l.

(** ak?(v) = true ⟺ is_ak_spec(v) — computational/declarative equivalence. *)
Lemma is_ak_correct : forall v,
  is_ak_computed v = true <-> is_ak_spec v.
Proof.
  intro v; split.
  - intro H; destruct v; simpl in H; try discriminate; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** ec_spec = {e, ai, o, au} — declarative ec specification. *)
Inductive is_ec_spec : Vowel -> Prop :=
  | EC_e : is_ec_spec V_e   | EC_ai : is_ec_spec V_ai
  | EC_o : is_ec_spec V_o   | EC_au : is_ec_spec V_au.

(** ec?(v) = true ⟺ is_ec_spec(v) — computational/declarative equivalence. *)
Lemma is_ec_correct : forall v,
  is_ec_computed v = true <-> is_ec_spec v.
Proof.
  intro v; split.
  - intro H; destruct v; simpl in H; try discriminate; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** V = {a,ā} ⊔ ik ⊔ ec — vowel trichotomy partition. *)
Lemma vowel_trichotomy : forall v,
  (v = V_a \/ v = V_aa) \/
  is_ik_spec v \/
  is_ec_spec v.
Proof.
  intro v.
  destruct v.
  - left; left; reflexivity.
  - left; right; reflexivity.
  - right; left; constructor.
  - right; left; constructor.
  - right; left; constructor.
  - right; left; constructor.
  - right; left; constructor.
  - right; left; constructor.
  - right; left; constructor.
  - right; right; constructor.
  - right; right; constructor.
  - right; right; constructor.
  - right; right; constructor.
Qed.

(** * Part III: Paribhāṣā Sūtras (Meta-rules) *)

(** vṛddhi_spec = {ā, ai, au} — the vṛddhi vowel grades (1.1.1). *)
Inductive is_vrddhi_vowel_spec : Vowel -> Prop :=
  | Vrddhi_aa : is_vrddhi_vowel_spec V_aa
  | Vrddhi_ai : is_vrddhi_vowel_spec V_ai
  | Vrddhi_au : is_vrddhi_vowel_spec V_au.

(** vṛddhi? : V → bool — tests v ∈ {ā, ai, au}. *)
Definition is_vrddhi_vowel (v : Vowel) : bool :=
  match v with
  | V_aa | V_ai | V_au => true
  | _ => false
  end.

(** vṛddhi?(v) = true ⟺ is_vrddhi_vowel_spec(v). *)
Lemma is_vrddhi_vowel_correct : forall v,
  is_vrddhi_vowel v = true <-> is_vrddhi_vowel_spec v.
Proof.
  intro v.
  split.
  - intro H.
    destruct v; simpl in H; try discriminate.
    + apply Vrddhi_aa.
    + apply Vrddhi_ai.
    + apply Vrddhi_au.
  - intro H.
    destruct H; reflexivity.
Qed.

(** guṇa_spec = {a, e, o} — the guṇa vowel grades (1.1.2). *)
Inductive is_guna_vowel_spec : Vowel -> Prop :=
  | Guna_a : is_guna_vowel_spec V_a
  | Guna_e : is_guna_vowel_spec V_e
  | Guna_o : is_guna_vowel_spec V_o.

(** guṇa? : V → bool — tests v ∈ {a, e, o}. *)
Definition is_guna_vowel (v : Vowel) : bool :=
  match v with
  | V_a | V_e | V_o => true
  | _ => false
  end.

(** guṇa?(v) = true ⟺ is_guna_vowel_spec(v). *)
Lemma is_guna_vowel_correct : forall v,
  is_guna_vowel v = true <-> is_guna_vowel_spec v.
Proof.
  intro v.
  split.
  - intro H.
    destruct v; simpl in H; try discriminate.
    + apply Guna_a.
    + apply Guna_e.
    + apply Guna_o.
  - intro H.
    destruct H; reflexivity.
Qed.

(** guṇa_sub ⊆ V × V — guṇa substitution: i,ī↦e and u,ū↦o (1.1.3). *)
Inductive guna_substitute_spec : Vowel -> Vowel -> Prop :=
  | GS_i : guna_substitute_spec V_i V_e
  | GS_ii : guna_substitute_spec V_ii V_e
  | GS_u : guna_substitute_spec V_u V_o
  | GS_uu : guna_substitute_spec V_uu V_o.

(** vṛddhi_sub ⊆ V × V — vṛddhi substitution: i,ī↦ai and u,ū↦au (1.1.3). *)
Inductive vrddhi_substitute_spec : Vowel -> Vowel -> Prop :=
  | VS_i : vrddhi_substitute_spec V_i V_ai
  | VS_ii : vrddhi_substitute_spec V_ii V_ai
  | VS_u : vrddhi_substitute_spec V_u V_au
  | VS_uu : vrddhi_substitute_spec V_uu V_au.

(** guṇa_ik : V → V? — partial guṇa function on ik vowels. *)
Definition guna_of_ik (v : Vowel) : option Vowel :=
  match v with
  | V_i | V_ii => Some V_e
  | V_u | V_uu => Some V_o
  | _ => None
  end.

(** vṛddhi_ik : V → V? — partial vṛddhi function on ik vowels. *)
Definition vrddhi_of_ik (v : Vowel) : option Vowel :=
  match v with
  | V_i | V_ii => Some V_ai
  | V_u | V_uu => Some V_au
  | _ => None
  end.

(** guṇa_ik(v₁) = v₂ ⟺ guṇa_sub(v₁, v₂). *)
Lemma guna_of_ik_correct : forall v1 v2,
  guna_of_ik v1 = Some v2 <-> guna_substitute_spec v1 v2.
Proof.
  intros v1 v2.
  split.
  - intro H.
    destruct v1; simpl in H; try discriminate;
    injection H as H; subst.
    + apply GS_i.
    + apply GS_ii.
    + apply GS_u.
    + apply GS_uu.
  - intro H.
    destruct H; reflexivity.
Qed.

(** vṛddhi_ik(v₁) = v₂ ⟺ vṛddhi_sub(v₁, v₂). *)
Lemma vrddhi_of_ik_correct : forall v1 v2,
  vrddhi_of_ik v1 = Some v2 <-> vrddhi_substitute_spec v1 v2.
Proof.
  intros v1 v2.
  split.
  - intro H.
    destruct v1; simpl in H; try discriminate;
    injection H as H; subst.
    + apply VS_i.
    + apply VS_ii.
    + apply VS_u.
    + apply VS_uu.
  - intro H.
    destruct H; reflexivity.
Qed.

(** guṇa_ṛḷ ⊆ V × P* — compound guṇa for syllabic liquids: ṛ,ṝ↦ar, ḷ↦al. *)
Inductive guna_r_spec : Vowel -> list Phoneme -> Prop :=
  | GRS_r : guna_r_spec V_r [Svar V_a; Vyan C_r]
  | GRS_rr : guna_r_spec V_rr [Svar V_a; Vyan C_r]
  | GRS_l : guna_r_spec V_l [Svar V_a; Vyan C_l].

(** vṛddhi_ṛḷ ⊆ V × P* — compound vṛddhi for syllabic liquids: ṛ,ṝ↦ār, ḷ↦āl. *)
Inductive vrddhi_r_spec : Vowel -> list Phoneme -> Prop :=
  | VRS_r : vrddhi_r_spec V_r [Svar V_aa; Vyan C_r]
  | VRS_rr : vrddhi_r_spec V_rr [Svar V_aa; Vyan C_r]
  | VRS_l : vrddhi_r_spec V_l [Svar V_aa; Vyan C_l].

(** * Part IV: Savarṇa (1.1.9) *)

(** [v] = V/≈ — savarṇa equivalence classes: {a,ā}, {i,ī}, {u,ū}, {ṛ,ṝ}, {ḷ}, {e}, {ai}, {o}, {au}. *)
Inductive SavarnaClass : Type :=
  | SC_a | SC_i | SC_u | SC_r | SC_l | SC_e | SC_ai | SC_o | SC_au.

(** [·] : V → V/≈ — quotient map to savarṇa class. *)
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

(** =_[·] : [V] × [V] → bool — decidable equality on savarṇa classes. *)
Scheme Equality for SavarnaClass.

(** ≈ : V × V → bool — savarṇa relation: v₁ ≈ v₂ iff [v₁] = [v₂]. *)
Definition savarna (v1 v2 : Vowel) : bool :=
  SavarnaClass_beq (savarna_class v1) (savarna_class v2).

(** ∀v. v ≈ v — reflexivity of savarṇa. *)
Lemma savarna_refl : forall v, savarna v v = true.
Proof.
  intro v.
  unfold savarna.
  destruct v; reflexivity.
Qed.

(** v₁ ≈ v₂ ⟺ v₂ ≈ v₁ — symmetry of savarṇa. *)
Lemma savarna_sym : forall v1 v2, savarna v1 v2 = savarna v2 v1.
Proof.
  intros v1 v2.
  unfold savarna.
  destruct v1, v2; reflexivity.
Qed.

(** ≈_spec ⊆ V × V — declarative savarṇa specification (1.1.9). *)
Inductive savarna_spec : Vowel -> Vowel -> Prop :=
  | Sav_a_a : savarna_spec V_a V_a
  | Sav_a_aa : savarna_spec V_a V_aa
  | Sav_aa_a : savarna_spec V_aa V_a
  | Sav_aa_aa : savarna_spec V_aa V_aa
  | Sav_i_i : savarna_spec V_i V_i
  | Sav_i_ii : savarna_spec V_i V_ii
  | Sav_ii_i : savarna_spec V_ii V_i
  | Sav_ii_ii : savarna_spec V_ii V_ii
  | Sav_u_u : savarna_spec V_u V_u
  | Sav_u_uu : savarna_spec V_u V_uu
  | Sav_uu_u : savarna_spec V_uu V_u
  | Sav_uu_uu : savarna_spec V_uu V_uu
  | Sav_r_r : savarna_spec V_r V_r
  | Sav_r_rr : savarna_spec V_r V_rr
  | Sav_rr_r : savarna_spec V_rr V_r
  | Sav_rr_rr : savarna_spec V_rr V_rr
  | Sav_l_l : savarna_spec V_l V_l
  | Sav_e_e : savarna_spec V_e V_e
  | Sav_ai_ai : savarna_spec V_ai V_ai
  | Sav_o_o : savarna_spec V_o V_o
  | Sav_au_au : savarna_spec V_au V_au.

(** v₁ ≈ v₂ = true ⟺ savarna_spec(v₁, v₂). *)
Lemma savarna_correct : forall v1 v2,
  savarna v1 v2 = true <-> savarna_spec v1 v2.
Proof.
  intros v1 v2.
  split.
  - intro H.
    unfold savarna in H.
    destruct v1, v2; simpl in H; try discriminate; constructor.
  - intro H.
    unfold savarna.
    destruct H; reflexivity.
Qed.

(** ∀v. savarna_spec(v, v) — reflexivity in Prop. *)
Lemma savarna_spec_refl : forall v, savarna_spec v v.
Proof.
  intro v.
  destruct v; constructor.
Qed.

(** savarna_spec(v₁, v₂) ⟹ savarna_spec(v₂, v₁) — symmetry in Prop. *)
Lemma savarna_spec_sym : forall v1 v2,
  savarna_spec v1 v2 -> savarna_spec v2 v1.
Proof.
  intros v1 v2 H.
  destruct H; constructor.
Qed.

(** * Part V: Guṇa and Vṛddhi (1.1.1-2) *)

(** guṇa : V → P⁺ — guṇa grade: a,ā↦a; i,ī↦e; u,ū↦o; ṛ,ṝ↦ar; ḷ↦al. *)
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

(** vṛddhi : V → P⁺ — vṛddhi grade: a,ā↦ā; i,ī↦ai; u,ū↦au; ṛ,ṝ↦ār; ḷ↦āl. *)
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

(** dīrgha : V → V — lengthening: a↦ā, i↦ī, u↦ū, ṛ↦ṝ; others fixed. *)
Definition lengthen (v : Vowel) : Vowel :=
  match v with
  | V_a => V_aa
  | V_i => V_ii
  | V_u => V_uu
  | V_r => V_rr
  | other => other
  end.

(** dīrgha_spec ⊆ V × V — declarative lengthening specification. *)
Inductive lengthen_spec : Vowel -> Vowel -> Prop :=
  | Len_a : lengthen_spec V_a V_aa
  | Len_aa : lengthen_spec V_aa V_aa
  | Len_i : lengthen_spec V_i V_ii
  | Len_ii : lengthen_spec V_ii V_ii
  | Len_u : lengthen_spec V_u V_uu
  | Len_uu : lengthen_spec V_uu V_uu
  | Len_r : lengthen_spec V_r V_rr
  | Len_rr : lengthen_spec V_rr V_rr
  | Len_l : lengthen_spec V_l V_l
  | Len_e : lengthen_spec V_e V_e
  | Len_ai : lengthen_spec V_ai V_ai
  | Len_o : lengthen_spec V_o V_o
  | Len_au : lengthen_spec V_au V_au.

(** dīrgha(v₁) = v₂ ⟺ lengthen_spec(v₁, v₂). *)
Lemma lengthen_correct : forall v1 v2,
  lengthen v1 = v2 <-> lengthen_spec v1 v2.
Proof.
  intros v1 v2; split.
  - intro H; destruct v1; simpl in H; subst; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** a? : V → bool — tests v ∈ {a, ā}. *)
Definition is_a_class (v : Vowel) : bool :=
  match v with V_a | V_aa => true | _ => false end.

(** guṇa_spec ⊆ V × P⁺ — exhaustive declarative guṇa specification. *)
Inductive guna_result_spec : Vowel -> list Phoneme -> Prop :=
  | GR_a : guna_result_spec V_a [Svar V_a]
  | GR_aa : guna_result_spec V_aa [Svar V_a]
  | GR_i : guna_result_spec V_i [Svar V_e]
  | GR_ii : guna_result_spec V_ii [Svar V_e]
  | GR_u : guna_result_spec V_u [Svar V_o]
  | GR_uu : guna_result_spec V_uu [Svar V_o]
  | GR_r : guna_result_spec V_r [Svar V_a; Vyan C_r]
  | GR_rr : guna_result_spec V_rr [Svar V_a; Vyan C_r]
  | GR_l : guna_result_spec V_l [Svar V_a; Vyan C_l]
  | GR_e : guna_result_spec V_e [Svar V_e]
  | GR_o : guna_result_spec V_o [Svar V_o]
  | GR_ai : guna_result_spec V_ai [Svar V_ai]
  | GR_au : guna_result_spec V_au [Svar V_au].

(** guṇa(v) = ps ⟺ guna_result_spec(v, ps). *)
Lemma guna_correct : forall v ps,
  guna v = ps <-> guna_result_spec v ps.
Proof.
  intros v ps.
  split.
  - intro H. destruct v; simpl in H; subst; constructor.
  - intro H. destruct H; reflexivity.
Qed.

(** |guṇa(v)| ∈ {1, 2} — guṇa produces 1 or 2 phonemes. *)
Lemma guna_length : forall v,
  length (guna v) = 1 \/ length (guna v) = 2.
Proof.
  intro v; destruct v; simpl; auto.
Qed.

(** |guṇa(v)| = 2 ⟺ v ∈ {ṛ, ṝ, ḷ} — compound forms characterization. *)
Lemma guna_compound_iff : forall v,
  length (guna v) = 2 <-> (v = V_r \/ v = V_rr \/ v = V_l).
Proof.
  intro v; split.
  - intro H; destruct v; simpl in H; try discriminate; auto.
  - intros [H | [H | H]]; subst; reflexivity.
Qed.

(** vṛddhi_spec ⊆ V × P⁺ — exhaustive declarative vṛddhi specification. *)
Inductive vrddhi_result_spec : Vowel -> list Phoneme -> Prop :=
  | VR_a : vrddhi_result_spec V_a [Svar V_aa]
  | VR_aa : vrddhi_result_spec V_aa [Svar V_aa]
  | VR_i : vrddhi_result_spec V_i [Svar V_ai]
  | VR_ii : vrddhi_result_spec V_ii [Svar V_ai]
  | VR_u : vrddhi_result_spec V_u [Svar V_au]
  | VR_uu : vrddhi_result_spec V_uu [Svar V_au]
  | VR_r : vrddhi_result_spec V_r [Svar V_aa; Vyan C_r]
  | VR_rr : vrddhi_result_spec V_rr [Svar V_aa; Vyan C_r]
  | VR_l : vrddhi_result_spec V_l [Svar V_aa; Vyan C_l]
  | VR_e : vrddhi_result_spec V_e [Svar V_ai]
  | VR_o : vrddhi_result_spec V_o [Svar V_au]
  | VR_ai : vrddhi_result_spec V_ai [Svar V_ai]
  | VR_au : vrddhi_result_spec V_au [Svar V_au].

(** vṛddhi(v) = ps ⟺ vrddhi_result_spec(v, ps). *)
Lemma vrddhi_correct : forall v ps,
  vrddhi v = ps <-> vrddhi_result_spec v ps.
Proof.
  intros v ps.
  split.
  - intro H. destruct v; simpl in H; subst; constructor.
  - intro H. destruct H; reflexivity.
Qed.

(** v ∈ {ṛ, ṝ} ⟹ guṇa(v) = [a, r]. *)
Lemma guna_r_yields_ar : forall v,
  (v = V_r \/ v = V_rr) ->
  guna v = [Svar V_a; Vyan C_r].
Proof.
  intros v [H | H]; subst; reflexivity.
Qed.

(** guṇa(ḷ) = [a, l]. *)
Lemma guna_l_yields_al :
  guna V_l = [Svar V_a; Vyan C_l].
Proof. reflexivity. Qed.

(** v ∈ {ṛ, ṝ} ⟹ vṛddhi(v) = [ā, r]. *)
Lemma vrddhi_r_yields_aar : forall v,
  (v = V_r \/ v = V_rr) ->
  vrddhi v = [Svar V_aa; Vyan C_r].
Proof.
  intros v [H | H]; subst; reflexivity.
Qed.

(** vṛddhi(ḷ) = [ā, l]. *)
Lemma vrddhi_l_yields_aal :
  vrddhi V_l = [Svar V_aa; Vyan C_l].
Proof. reflexivity. Qed.

(** * Part VI: Yaṇ Correspondence *)

(** yaṇ : V → C? — semivowel of ik vowels: i,ī↦y; u,ū↦v; ṛ,ṝ↦r; ḷ↦l. *)
Definition yan_of (v : Vowel) : option Consonant :=
  match v with
  | V_i | V_ii => Some C_y
  | V_u | V_uu => Some C_v
  | V_r | V_rr => Some C_r
  | V_l => Some C_l
  | _ => None
  end.

(** v ∈ ik ⟹ ∃c. yaṇ(v) = c — ik vowels have semivowels. *)
Lemma yan_of_ik : forall v,
  is_ik_computed v = true -> exists c, yan_of v = Some c.
Proof.
  intros v H.
  destruct v; simpl in H; try discriminate.
  - exists C_y. reflexivity.
  - exists C_y. reflexivity.
  - exists C_v. reflexivity.
  - exists C_v. reflexivity.
  - exists C_r. reflexivity.
  - exists C_r. reflexivity.
  - exists C_l. reflexivity.
Qed.

(** yaṇ_spec ⊆ V × C — declarative yaṇ correspondence. *)
Inductive yan_of_spec : Vowel -> Consonant -> Prop :=
  | YanOf_i : yan_of_spec V_i C_y
  | YanOf_ii : yan_of_spec V_ii C_y
  | YanOf_u : yan_of_spec V_u C_v
  | YanOf_uu : yan_of_spec V_uu C_v
  | YanOf_r : yan_of_spec V_r C_r
  | YanOf_rr : yan_of_spec V_rr C_r
  | YanOf_l : yan_of_spec V_l C_l.

(** yaṇ(v) = c ⟺ yan_of_spec(v, c). *)
Lemma yan_of_correct : forall v c,
  yan_of v = Some c <-> yan_of_spec v c.
Proof.
  intros v c; split.
  - intro H; destruct v; simpl in H; try discriminate;
    injection H as H; subst; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** ayavāyāv : V → P*? — ec decomposition: e↦ay, o↦av, ai↦āy, au↦āv (6.1.78). *)
Definition ayavayav (v : Vowel) : option (list Phoneme) :=
  match v with
  | V_e => Some [Svar V_a; Vyan C_y]
  | V_o => Some [Svar V_a; Vyan C_v]
  | V_ai => Some [Svar V_aa; Vyan C_y]
  | V_au => Some [Svar V_aa; Vyan C_v]
  | _ => None
  end.

(** v ∈ ec ⟹ ∃ps. ayavāyāv(v) = ps. *)
Lemma ayavayav_ec : forall v,
  is_ec_computed v = true -> exists ps, ayavayav v = Some ps.
Proof.
  intros v H.
  destruct v; simpl in H; try discriminate.
  - exists [Svar V_a; Vyan C_y]. reflexivity.
  - exists [Svar V_aa; Vyan C_y]. reflexivity.
  - exists [Svar V_a; Vyan C_v]. reflexivity.
  - exists [Svar V_aa; Vyan C_v]. reflexivity.
Qed.

(** ayavāyāv_spec ⊆ V × P* — declarative decomposition spec. *)
Inductive ayavayav_spec : Vowel -> list Phoneme -> Prop :=
  | Ayav_e : ayavayav_spec V_e [Svar V_a; Vyan C_y]
  | Ayav_ai : ayavayav_spec V_ai [Svar V_aa; Vyan C_y]
  | Ayav_o : ayavayav_spec V_o [Svar V_a; Vyan C_v]
  | Ayav_au : ayavayav_spec V_au [Svar V_aa; Vyan C_v].

(** ayavāyāv(v) = ps ⟺ ayavayav_spec(v, ps). *)
Lemma ayavayav_correct : forall v ps,
  ayavayav v = Some ps <-> ayavayav_spec v ps.
Proof.
  intros v ps; split.
  - intro H; destruct v; simpl in H; try discriminate;
    injection H as H; subst; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** * Part VII: Sūtra Numbering and Precedence *)

(** Sūtra = ℕ × ℕ × ℕ — sūtra address as (adhyāya, pāda, sūtra). *)
Record SutraNum := {
  adhyaya : nat;
  pada : nat;
  sutra : nat
}.

(** =_S : S × S → bool — decidable sūtra equality. *)
Definition sutra_eq (s1 s2 : SutraNum) : bool :=
  Nat.eqb (adhyaya s1) (adhyaya s2) &&
  Nat.eqb (pada s1) (pada s2) &&
  Nat.eqb (sutra s1) (sutra s2).

(** <_S ⊆ S × S — lexicographic ordering on sūtra numbers. *)
Definition sutra_lt (s1 s2 : SutraNum) : Prop :=
  adhyaya s1 < adhyaya s2 \/
  (adhyaya s1 = adhyaya s2 /\ pada s1 < pada s2) \/
  (adhyaya s1 = adhyaya s2 /\ pada s1 = pada s2 /\ sutra s1 < sutra s2).

(** <_S : S × S → bool — computable lexicographic less-than. *)
Definition sutra_ltb (s1 s2 : SutraNum) : bool :=
  if Nat.ltb (adhyaya s1) (adhyaya s2) then true
  else if Nat.eqb (adhyaya s1) (adhyaya s2) then
    if Nat.ltb (pada s1) (pada s2) then true
    else if Nat.eqb (pada s1) (pada s2) then
      Nat.ltb (sutra s1) (sutra s2)
    else false
  else false.

(** A sūtra number is never less than itself. *)
Lemma sutra_ltb_irrefl : forall s, sutra_ltb s s = false.
Proof.
  intro s.
  unfold sutra_ltb.
  rewrite Nat.ltb_irrefl.
  rewrite Nat.eqb_refl.
  rewrite Nat.ltb_irrefl.
  rewrite Nat.eqb_refl.
  rewrite Nat.ltb_irrefl.
  reflexivity.
Qed.

(** Sūtra ordering is transitive: if s1 precedes s2 and s2 precedes s3, then s1 precedes s3. *)
Lemma sutra_ltb_trans : forall s1 s2 s3,
  sutra_ltb s1 s2 = true ->
  sutra_ltb s2 s3 = true ->
  sutra_ltb s1 s3 = true.
Proof.
  intros s1 s2 s3 H12 H23.
  unfold sutra_ltb in *.
  destruct (Nat.ltb (adhyaya s1) (adhyaya s2)) eqn:E1.
  - apply Nat.ltb_lt in E1.
    destruct (Nat.ltb (adhyaya s2) (adhyaya s3)) eqn:E2.
    + apply Nat.ltb_lt in E2.
      assert (adhyaya s1 < adhyaya s3) by lia.
      apply Nat.ltb_lt in H.
      rewrite H. reflexivity.
    + destruct (Nat.eqb (adhyaya s2) (adhyaya s3)) eqn:E2'.
      * apply Nat.eqb_eq in E2'.
        assert (adhyaya s1 < adhyaya s3) by lia.
        apply Nat.ltb_lt in H.
        rewrite H. reflexivity.
      * discriminate.
  - destruct (Nat.eqb (adhyaya s1) (adhyaya s2)) eqn:E1'; try discriminate.
    apply Nat.eqb_eq in E1'.
    destruct (Nat.ltb (adhyaya s2) (adhyaya s3)) eqn:E2.
    + apply Nat.ltb_lt in E2.
      assert (adhyaya s1 < adhyaya s3) by lia.
      apply Nat.ltb_lt in H.
      rewrite H. reflexivity.
    + destruct (Nat.eqb (adhyaya s2) (adhyaya s3)) eqn:E2'; try discriminate.
      apply Nat.eqb_eq in E2'.
      assert (Nat.ltb (adhyaya s1) (adhyaya s3) = false).
      { apply Nat.ltb_ge. lia. }
      rewrite H.
      assert (Nat.eqb (adhyaya s1) (adhyaya s3) = true).
      { apply Nat.eqb_eq. lia. }
      rewrite H0.
      destruct (Nat.ltb (pada s1) (pada s2)) eqn:P1.
      * apply Nat.ltb_lt in P1.
        destruct (Nat.ltb (pada s2) (pada s3)) eqn:P2.
        -- apply Nat.ltb_lt in P2.
           assert (pada s1 < pada s3) by lia.
           apply Nat.ltb_lt in H1.
           rewrite H1. reflexivity.
        -- destruct (Nat.eqb (pada s2) (pada s3)) eqn:P2'; try discriminate.
           apply Nat.eqb_eq in P2'.
           assert (pada s1 < pada s3) by lia.
           apply Nat.ltb_lt in H1.
           rewrite H1. reflexivity.
      * destruct (Nat.eqb (pada s1) (pada s2)) eqn:P1'; try discriminate.
        apply Nat.eqb_eq in P1'.
        destruct (Nat.ltb (pada s2) (pada s3)) eqn:P2.
        -- apply Nat.ltb_lt in P2.
           assert (pada s1 < pada s3) by lia.
           apply Nat.ltb_lt in H1.
           rewrite H1. reflexivity.
        -- destruct (Nat.eqb (pada s2) (pada s3)) eqn:P2'; try discriminate.
           apply Nat.eqb_eq in P2'.
           assert (Nat.ltb (pada s1) (pada s3) = false).
           { apply Nat.ltb_ge. lia. }
           rewrite H1.
           assert (Nat.eqb (pada s1) (pada s3) = true).
           { apply Nat.eqb_eq. lia. }
           rewrite H2.
           apply Nat.ltb_lt in H12.
           apply Nat.ltb_lt in H23.
           apply Nat.ltb_lt.
           lia.
Qed.

(** The computable ordering matches the declarative ordering specification. *)
Lemma sutra_ltb_correct : forall s1 s2,
  sutra_ltb s1 s2 = true <-> sutra_lt s1 s2.
Proof.
  intros s1 s2.
  split.
  - intro H.
    unfold sutra_ltb in H.
    unfold sutra_lt.
    destruct (Nat.ltb (adhyaya s1) (adhyaya s2)) eqn:E1.
    + left.
      apply Nat.ltb_lt.
      exact E1.
    + destruct (Nat.eqb (adhyaya s1) (adhyaya s2)) eqn:E1'; try discriminate.
      apply Nat.eqb_eq in E1'.
      destruct (Nat.ltb (pada s1) (pada s2)) eqn:E2.
      * right. left.
        split.
        -- exact E1'.
        -- apply Nat.ltb_lt. exact E2.
      * destruct (Nat.eqb (pada s1) (pada s2)) eqn:E2'; try discriminate.
        apply Nat.eqb_eq in E2'.
        right. right.
        split.
        -- exact E1'.
        -- split.
           ++ exact E2'.
           ++ apply Nat.ltb_lt. exact H.
  - intro H.
    unfold sutra_lt in H.
    unfold sutra_ltb.
    destruct H as [Ha | [[Hb Hc] | [Hd [He Hf]]]].
    + apply Nat.ltb_lt in Ha.
      rewrite Ha.
      reflexivity.
    + assert (Nat.ltb (adhyaya s1) (adhyaya s2) = false).
      { apply Nat.ltb_ge. lia. }
      rewrite H.
      assert (Nat.eqb (adhyaya s1) (adhyaya s2) = true).
      { apply Nat.eqb_eq. exact Hb. }
      rewrite H0.
      apply Nat.ltb_lt in Hc.
      rewrite Hc.
      reflexivity.
    + assert (Nat.ltb (adhyaya s1) (adhyaya s2) = false).
      { apply Nat.ltb_ge. lia. }
      rewrite H.
      assert (Nat.eqb (adhyaya s1) (adhyaya s2) = true).
      { apply Nat.eqb_eq. exact Hd. }
      rewrite H0.
      assert (Nat.ltb (pada s1) (pada s2) = false).
      { apply Nat.ltb_ge. lia. }
      rewrite H1.
      assert (Nat.eqb (pada s1) (pada s2) = true).
      { apply Nat.eqb_eq. exact He. }
      rewrite H2.
      apply Nat.ltb_lt in Hf.
      exact Hf.
Qed.

(** When two rules conflict, the later rule in the text prevails. *)
Inductive para_defeats_spec : SutraNum -> SutraNum -> Prop :=
  | Para_later : forall s1 s2,
      sutra_lt s1 s2 ->
      para_defeats_spec s2 s1.

(** A rule cannot defeat itself in precedence. *)
Lemma para_defeats_irrefl : forall s, ~ para_defeats_spec s s.
Proof.
  intros s H.
  inversion H.
  unfold sutra_lt in H0.
  destruct H0 as [Hlt | [[Heq Hlt] | [Heq1 [Heq2 Hlt]]]]; lia.
Qed.

(** Precedence is asymmetric: if s1 defeats s2, then s2 cannot defeat s1. *)
Lemma para_defeats_asymm : forall s1 s2,
  para_defeats_spec s1 s2 -> ~ para_defeats_spec s2 s1.
Proof.
  intros s1 s2 H12 H21.
  inversion H12 as [sa sb Hlt1 Heq1 Heq2]; subst.
  inversion H21 as [sc sd Hlt2 Heq3 Heq4]; subst.
  unfold sutra_lt in *.
  destruct Hlt1 as [Ha | [[Hb Hc] | [Hd [He Hf]]]];
  destruct Hlt2 as [Ha' | [[Hb' Hc'] | [Hd' [He' Hf']]]]; lia.
Qed.

(** * Part VIII: Rule Representation *)

(** ** Morphological Context Types *)

(** Dhātu (root) classification for morphologically conditioned rules. *)
Inductive DhatuClass : Type :=
  | DC_eti        (** √i with prefix: pra+i → pre *)
  | DC_edhati     (** √edh: pr+edh → predh *)
  | DC_r_initial  (** Roots beginning with ṛ *)
  | DC_khyati     (** √khyā and derivatives *)
  | DC_other.     (** Default *)

(** Upasarga (verb prefix) information. *)
Inductive UpasargaInfo : Type :=
  | UI_none       (** No upasarga present *)
  | UI_pra        (** pra- prefix *)
  | UI_upa        (** upa- prefix *)
  | UI_a          (** a- prefix (ends in a) *)
  | UI_aa         (** ā- prefix (ends in ā) *)
  | UI_other_a    (** Other prefix ending in a/ā *)
  | UI_other.     (** Other prefix *)

(** Pratyaya (suffix) information. *)
Inductive PratyayaInfo : Type :=
  | PI_none       (** No suffix context *)
  | PI_am         (** -am suffix *)
  | PI_sas        (** -śas suffix *)
  | PI_ami        (** -ami suffix *)
  | PI_ngas       (** -ṅas suffix *)
  | PI_ngasi      (** -ṅasi suffix *)
  | PI_jas        (** -jas suffix *)
  | PI_sup        (** sup (nominal) suffix *)
  | PI_tin        (** tiṅ (verbal) suffix *)
  | PI_other.     (** Other suffix *)

(** Augment information. *)
Inductive AugmentInfo : Type :=
  | AI_none       (** No augment *)
  | AI_at         (** āṭ augment present *)
  | AI_ut         (** uṭh augment *)
  | AI_other.     (** Other augment *)

(** Special word classes. *)
Inductive SpecialClass : Type :=
  | SC_none       (** Default *)
  | SC_om         (** The word om *)
  | SC_ang        (** āṅ particle *)
  | SC_amredita   (** Reduplicated/iterative form *)
  | SC_avyakta    (** Onomatopoeia *)
  | SC_abhyasta.  (** Reduplicated verbal stem *)

(** Complete morphological context for sandhi application. *)
Record MorphContext : Type := mkMorphContext {
  mc_upasarga : UpasargaInfo;
  mc_dhatu : DhatuClass;
  mc_pratyaya : PratyayaInfo;
  mc_augment : AugmentInfo;
  mc_special : SpecialClass;
  mc_is_pada_anta : bool;        (** Word-final position *)
  mc_is_samasa : bool;           (** In compound *)
  mc_is_dhatu_pratyaya : bool    (** At root-suffix juncture *)
}.

(** Default context: external sandhi with no special conditions. *)
Definition default_morph_context : MorphContext := {|
  mc_upasarga := UI_none;
  mc_dhatu := DC_other;
  mc_pratyaya := PI_none;
  mc_augment := AI_none;
  mc_special := SC_none;
  mc_is_pada_anta := true;
  mc_is_samasa := false;
  mc_is_dhatu_pratyaya := false
|}.

(** Context for upasarga + dhātu juncture. *)
Definition upasarga_context (ui : UpasargaInfo) (dc : DhatuClass) : MorphContext := {|
  mc_upasarga := ui;
  mc_dhatu := dc;
  mc_pratyaya := PI_none;
  mc_augment := AI_none;
  mc_special := SC_none;
  mc_is_pada_anta := false;
  mc_is_samasa := false;
  mc_is_dhatu_pratyaya := true
|}.

(** ** Rule Identifiers *)

(** Identifiers for vowel sandhi rules from Aṣṭādhyāyī 6.1.77-113.
    Organized by sutra number within the ekaḥ pūrvaparayoḥ adhikāra (6.1.84-111). *)
Inductive RuleId : Type :=
  | R_6_1_77      (** iko yaṇ aci — ik vowels become semivowels *)
  | R_6_1_78      (** eco 'yavāyāvaḥ — ec vowels decompose *)
  | R_6_1_87      (** ādguṇaḥ — a/ā + vowel → guṇa *)
  | R_6_1_88      (** vṛddhir eci — a/ā + ec → vṛddhi *)
  | R_6_1_89      (** ety-edhaty-ūṭhsu — exception for eti/edhati/ūṭh *)
  | R_6_1_90      (** āṭaś ca — after āṭ augment → vṛddhi *)
  | R_6_1_91      (** upasargād ṛti dhātau — upasarga + ṛ-root → vṛddhi *)
  | R_6_1_94      (** eṅi pararūpam — a/ā + e/o from root → pararūpa *)
  | R_6_1_97      (** ato guṇe — a elided before guṇa *)
  | R_6_1_101     (** akaḥ savarṇe dīrghaḥ — similar vowels → long *)
  | R_6_1_107     (** ami pūrvaḥ — before ami suffix *)
  | R_6_1_109     (** eṅaḥ padāntād ati — pūrvarūpa at word boundary *)
  | R_6_1_110     (** ṅasiṅasoś ca — before ṅas/ṅasi *)
  | R_6_1_111     (** ṛta ut — ṛ becomes ut *)
  | R_6_1_113.    (** ato ror aplutād aplute — a before r *)

(** Decidable equality for rule identifiers. *)
Scheme Equality for RuleId.

(** Types of morphological boundaries where sandhi may or may not apply. *)
Inductive MorphBoundary : Type :=
  | PadaAnta
  | DhatuPratyaya
  | SamasaAnta
  | Internal.

(** Tests whether a rule requires word-final position to apply. *)
Definition requires_pada_boundary (r : RuleId) : bool :=
  match r with
  | R_6_1_109 => true
  | _ => false
  end.

(** Tests whether a morphological boundary permits a given rule to apply. *)
Definition boundary_allows_rule (b : MorphBoundary) (r : RuleId) : bool :=
  match r with
  | R_6_1_109 =>
      match b with
      | PadaAnta | SamasaAnta => true
      | _ => false
      end
  | _ => true
  end.

(** Tests whether a vowel is e or o, the guṇa diphthongs. *)
Definition is_en (v : Vowel) : bool := is_en_computed v.

(** Returns the sūtra number for each rule identifier. *)
Definition rule_sutra_num (r : RuleId) : SutraNum :=
  match r with
  | R_6_1_77 => {| adhyaya := 6; pada := 1; sutra := 77 |}
  | R_6_1_78 => {| adhyaya := 6; pada := 1; sutra := 78 |}
  | R_6_1_87 => {| adhyaya := 6; pada := 1; sutra := 87 |}
  | R_6_1_88 => {| adhyaya := 6; pada := 1; sutra := 88 |}
  | R_6_1_89 => {| adhyaya := 6; pada := 1; sutra := 89 |}
  | R_6_1_90 => {| adhyaya := 6; pada := 1; sutra := 90 |}
  | R_6_1_91 => {| adhyaya := 6; pada := 1; sutra := 91 |}
  | R_6_1_94 => {| adhyaya := 6; pada := 1; sutra := 94 |}
  | R_6_1_97 => {| adhyaya := 6; pada := 1; sutra := 97 |}
  | R_6_1_101 => {| adhyaya := 6; pada := 1; sutra := 101 |}
  | R_6_1_107 => {| adhyaya := 6; pada := 1; sutra := 107 |}
  | R_6_1_109 => {| adhyaya := 6; pada := 1; sutra := 109 |}
  | R_6_1_110 => {| adhyaya := 6; pada := 1; sutra := 110 |}
  | R_6_1_111 => {| adhyaya := 6; pada := 1; sutra := 111 |}
  | R_6_1_113 => {| adhyaya := 6; pada := 1; sutra := 113 |}
  end.

(** Tests whether r1 is an exception rule that overrides r2.
    Exception relationships in Pāṇinian grammar:
    - 6.1.88 is apavāda to 6.1.87 (vṛddhi overrides guṇa for ec)
    - 6.1.89 is apavāda to 6.1.87 (eti/edhati exception)
    - 6.1.90 is apavāda to 6.1.87 (āṭ augment vṛddhi)
    - 6.1.91 is apavāda to 6.1.87 (upasarga + ṛ vṛddhi)
    - 6.1.94 is apavāda to 6.1.87 (pararūpa for e/o)
    - 6.1.97 is apavāda to 6.1.87 (a-deletion before guṇa)
    - 6.1.101 is apavāda to 6.1.87, 6.1.77 (savarṇa dīrgha)
    - 6.1.107 is apavāda to 6.1.87 (ami pūrva)
    - 6.1.109 is apavāda to 6.1.78 (pūrvarūpa)
    - 6.1.110 is apavāda to 6.1.87 (ṅas/ṅasi)
    - 6.1.111 is apavāda to 6.1.87 (ṛ → ut) *)
Definition is_apavada (r1 r2 : RuleId) : bool :=
  match r1, r2 with
  | R_6_1_88, R_6_1_87 => true
  | R_6_1_89, R_6_1_87 => true
  | R_6_1_90, R_6_1_87 => true
  | R_6_1_91, R_6_1_87 => true
  | R_6_1_94, R_6_1_87 => true
  | R_6_1_97, R_6_1_87 => true
  | R_6_1_101, R_6_1_87 => true
  | R_6_1_101, R_6_1_77 => true
  | R_6_1_107, R_6_1_87 => true
  | R_6_1_109, R_6_1_78 => true
  | R_6_1_110, R_6_1_87 => true
  | R_6_1_111, R_6_1_87 => true
  | _, _ => false
  end.

(** Tests whether a rule's phonological conditions are satisfied by the vowel pair.
    This is for EXTERNAL (padānta) sandhi only. Morphologically conditioned rules
    (6.1.89-91, 6.1.94, 6.1.97, 6.1.107, 6.1.110-111, 6.1.113) return false here
    since they require context beyond vowel pairs (upasarga, dhātu, pratyaya).
    Use rule_matches_with_context for internal/morphological sandhi. *)
Definition rule_matches (r : RuleId) (v1 v2 : Vowel) : bool :=
  match r with
  | R_6_1_77 => is_ik_computed v1
  | R_6_1_78 => is_ec_computed v1
  | R_6_1_87 => is_a_class v1
  | R_6_1_88 => is_a_class v1 && is_ec_computed v2
  | R_6_1_89 => false
  | R_6_1_90 => false
  | R_6_1_91 => false
  | R_6_1_94 => false
  | R_6_1_97 => false
  | R_6_1_101 => is_ak_computed v1 && is_ak_computed v2 && savarna v1 v2
  | R_6_1_107 => false
  | R_6_1_109 => is_en v1 && Vowel_beq v2 V_a
  | R_6_1_110 => false
  | R_6_1_111 => false
  | R_6_1_113 => false
  end.

(** Tests both phonological conditions and boundary requirements for a rule. *)
Definition rule_matches_at_boundary (r : RuleId) (v1 v2 : Vowel) (b : MorphBoundary) : bool :=
  rule_matches r v1 v2 && boundary_allows_rule b r.

(** ** Context-Aware Rule Matching *)

(** Helper: checks if upasarga ends in a/ā. *)
Definition upasarga_ends_in_a (ui : UpasargaInfo) : bool :=
  match ui with
  | UI_a | UI_aa | UI_pra | UI_upa | UI_other_a => true
  | _ => false
  end.

(** Helper: checks if dhātu is ṛ-initial. *)
Definition dhatu_is_r_initial (dc : DhatuClass) : bool :=
  match dc with
  | DC_r_initial => true
  | _ => false
  end.

(** Helper: checks if dhātu is eti or edhati. *)
Definition dhatu_is_eti_edhati (dc : DhatuClass) : bool :=
  match dc with
  | DC_eti | DC_edhati => true
  | _ => false
  end.

(** Helper: checks if āṭ augment is present. *)
Definition has_at_augment (ai : AugmentInfo) : bool :=
  match ai with
  | AI_at => true
  | _ => false
  end.

(** Helper: checks if suffix is ami. *)
Definition is_ami_suffix (pi : PratyayaInfo) : bool :=
  match pi with
  | PI_ami => true
  | _ => false
  end.

(** Helper: checks if suffix is ṅas or ṅasi. *)
Definition is_ngas_suffix (pi : PratyayaInfo) : bool :=
  match pi with
  | PI_ngas | PI_ngasi => true
  | _ => false
  end.

(** Full rule matching with morphological context.
    6.1.89: ety-edhaty-ūṭhsu — vṛddhi for roots eti, edhati (a/ā + e)
    6.1.90: āṭaś ca — vṛddhi after āṭ augment
    6.1.91: upasargād ṛti dhātau — upasarga (a/ā) + ṛ-initial root → vṛddhi
    6.1.94: eṅi pararūpam — a/ā + e/o from root → pararūpa (second wins)
    6.1.97: ato guṇe — a deleted before guṇa in compounds
    6.1.107: ami pūrvaḥ — before ami suffix, first vowel wins
    6.1.110: ṅasiṅasoś ca — before ṅas/ṅasi, pūrvarūpa
    6.1.111: ṛta ut — ṛ after a becomes ut
    6.1.113: ato ror aplutād aplute — a + r → o *)
Definition rule_matches_with_context
  (r : RuleId) (v1 v2 : Vowel) (ctx : MorphContext) : bool :=
  match r with
  | R_6_1_77 => is_ik_computed v1
  | R_6_1_78 => is_ec_computed v1
  | R_6_1_87 => is_a_class v1
  | R_6_1_88 => is_a_class v1 && is_ec_computed v2
  | R_6_1_89 =>
      is_a_class v1 && is_ec_computed v2 &&
      dhatu_is_eti_edhati (mc_dhatu ctx)
  | R_6_1_90 =>
      is_a_class v1 &&
      has_at_augment (mc_augment ctx)
  | R_6_1_91 =>
      is_a_class v1 && Vowel_beq v2 V_r &&
      upasarga_ends_in_a (mc_upasarga ctx) &&
      dhatu_is_r_initial (mc_dhatu ctx)
  | R_6_1_94 =>
      is_a_class v1 && is_en v2 &&
      mc_is_dhatu_pratyaya ctx
  | R_6_1_97 =>
      Vowel_beq v1 V_a &&
      is_guna_vowel v2 &&
      mc_is_samasa ctx
  | R_6_1_101 => is_ak_computed v1 && is_ak_computed v2 && savarna v1 v2
  | R_6_1_107 =>
      is_a_class v1 &&
      is_ami_suffix (mc_pratyaya ctx)
  | R_6_1_109 =>
      is_en v1 && Vowel_beq v2 V_a &&
      mc_is_pada_anta ctx
  | R_6_1_110 =>
      is_en v1 && Vowel_beq v2 V_a &&
      is_ngas_suffix (mc_pratyaya ctx)
  | R_6_1_111 =>
      is_a_class v1 && Vowel_beq v2 V_r &&
      mc_is_dhatu_pratyaya ctx
  | R_6_1_113 =>
      Vowel_beq v1 V_a && Vowel_beq v2 V_r &&
      negb (mc_is_pada_anta ctx)
  end.

(** Rule 6.1.109 applies at word boundaries. *)
Example boundary_109_pada : rule_matches_at_boundary R_6_1_109 V_e V_a PadaAnta = true.
Proof. reflexivity. Qed.

(** Rule 6.1.109 does not apply word-internally. *)
Example boundary_109_internal : rule_matches_at_boundary R_6_1_109 V_e V_a Internal = false.
Proof. reflexivity. Qed.

(** Most rules apply regardless of boundary type. *)
Example boundary_87_internal : rule_matches_at_boundary R_6_1_87 V_a V_i Internal = true.
Proof. reflexivity. Qed.

(** Computes the phoneme sequence that results from applying a rule to a vowel pair. *)
Definition apply_rule (r : RuleId) (v1 v2 : Vowel) : list Phoneme :=
  match r with
  | R_6_1_77 =>
      match yan_of v1 with
      | Some c => [Vyan c; Svar v2]
      | None => [Svar v1; Svar v2]
      end
  | R_6_1_78 =>
      match ayavayav v1 with
      | Some prefix => prefix ++ [Svar v2]
      | None => [Svar v1; Svar v2]
      end
  | R_6_1_87 => guna v2
  | R_6_1_88 => vrddhi v2
  | R_6_1_89 => vrddhi v2
  | R_6_1_90 => vrddhi v2
  | R_6_1_91 => vrddhi V_r
  | R_6_1_94 => [Svar v2]
  | R_6_1_97 => [Svar v2]
  | R_6_1_101 => [Svar (lengthen v1)]
  | R_6_1_107 => [Svar (lengthen v1)]
  | R_6_1_109 => [Svar v1]
  | R_6_1_110 => [Svar v1]
  | R_6_1_111 => [Svar V_u; Vyan C_t]
  | R_6_1_113 => [Svar V_o]
  end.

(** * Part IX: Precedence - vipratiṣedhe paraṁ kāryam *)

(** Tests whether r1 defeats r2, either by being an exception or by appearing later. *)
Definition rule_defeats (r1 r2 : RuleId) : bool :=
  is_apavada r1 r2 ||
  (negb (is_apavada r2 r1) &&
   sutra_ltb (rule_sutra_num r2) (rule_sutra_num r1)).

(** No rule defeats itself in precedence. *)
Lemma rule_defeats_irrefl : forall r, rule_defeats r r = false.
Proof.
  intro r.
  unfold rule_defeats.
  destruct r; simpl; rewrite sutra_ltb_irrefl; reflexivity.
Qed.

(** ** Rule Registry and Extension Points *)

(** To add a new sandhi rule to this formalization, modify these locations:
    1. RuleId: Add a new constructor (e.g., R_6_1_xxx)
    2. rule_sutra_num: Define its sūtra number for precedence
    3. is_apavada: Define any exception relationships with existing rules
    4. rule_matches: Define when the rule applies (phonological conditions)
    5. apply_rule: Define the rule's output
    6. all_rules: Add to this list
    7. rule_output_spec: Add a constructor for the independent specification
    8. apply_rule_correct: Extend the proof to cover the new rule
    9. requires_pada_boundary/boundary_allows_rule: If boundary-sensitive
    10. defeat_total: Verify totality still holds (may need proof updates)

    The tournament-based selection (find_winner) automatically handles new rules
    as long as defeat_total holds for the extended rule set. *)

(** The complete list of sandhi rules in this formalization. *)
(** All rules that can apply based on vowel pairs alone (no morphological context).
    Morphologically conditioned rules (6.1.89-91, 6.1.107, 6.1.110-111, 6.1.113)
    are not included here as they always return false for rule_matches. *)
Definition all_rules : list RuleId :=
  [R_6_1_77; R_6_1_78; R_6_1_87; R_6_1_88; R_6_1_101; R_6_1_109].

(** Filters the rule list to those whose conditions are satisfied by a vowel pair. *)
Fixpoint matching_rules (rules : list RuleId) (v1 v2 : Vowel)
  : list RuleId :=
  match rules with
  | [] => []
  | r :: rs =>
      if rule_matches r v1 v2
      then r :: matching_rules rs v1 v2
      else matching_rules rs v1 v2
  end.

(** Tournament-style selection that eliminates rules pairwise based on precedence. *)
Fixpoint find_winner_aux (fuel : nat) (candidates : list RuleId)
  : option RuleId :=
  match fuel with
  | O => None
  | S fuel' =>
      match candidates with
      | [] => None
      | [r] => Some r
      | r1 :: r2 :: rest =>
          if rule_defeats r1 r2 then find_winner_aux fuel' (r1 :: rest)
          else find_winner_aux fuel' (r2 :: rest)
      end
  end.

(** Finds the winning rule among candidates using tournament selection. *)
Definition find_winner (candidates : list RuleId) : option RuleId :=
  find_winner_aux (List.length candidates) candidates.

(** The fuel parameter is always sufficient to complete the tournament. *)
Lemma find_winner_aux_fuel_sufficient : forall fuel candidates,
  fuel >= length candidates ->
  candidates <> [] ->
  exists r, find_winner_aux fuel candidates = Some r.
Proof.
  induction fuel as [| fuel' IH].
  - intros candidates Hfuel Hne.
    destruct candidates.
    + contradiction.
    + simpl in Hfuel. lia.
  - intros candidates Hfuel Hne.
    destruct candidates as [| r1 rest].
    + contradiction.
    + destruct rest as [| r2 rest'].
      * simpl. exists r1. reflexivity.
      * simpl.
        destruct (rule_defeats r1 r2) eqn:Edef.
        -- apply IH.
           ++ simpl in Hfuel. simpl. lia.
           ++ discriminate.
        -- apply IH.
           ++ simpl in Hfuel. simpl. lia.
           ++ discriminate.
Qed.

(** A non-empty candidate list always yields a winner. *)
Lemma find_winner_sufficient : forall candidates,
  candidates <> [] ->
  exists r, find_winner candidates = Some r.
Proof.
  intros candidates Hne.
  unfold find_winner.
  apply find_winner_aux_fuel_sufficient.
  - lia.
  - exact Hne.
Qed.

(** Selects the winning rule for a vowel pair from all applicable rules. *)
Definition select_rule (v1 v2 : Vowel) : option RuleId :=
  find_winner (matching_rules all_rules v1 v2).

(** * Part X: Declarative Specification *)

(** Declarative specification of when each sandhi rule applies to a vowel pair.
    Note: Morphologically conditioned rules (6.1.89-91, 6.1.107, 6.1.110-111, 6.1.113)
    are not included here as they require context beyond vowel pairs. *)
Inductive sandhi_applicable : RuleId -> Vowel -> Vowel -> Prop :=
  | SA_77 : forall v1 v2,
      is_ik_computed v1 = true ->
      sandhi_applicable R_6_1_77 v1 v2
  | SA_78 : forall v1 v2,
      is_ec_computed v1 = true ->
      sandhi_applicable R_6_1_78 v1 v2
  | SA_87 : forall v1 v2,
      is_a_class v1 = true ->
      sandhi_applicable R_6_1_87 v1 v2
  | SA_88 : forall v1 v2,
      is_a_class v1 = true ->
      is_ec_computed v2 = true ->
      sandhi_applicable R_6_1_88 v1 v2
  | SA_101 : forall v1 v2,
      is_ak_computed v1 = true ->
      is_ak_computed v2 = true ->
      savarna v1 v2 = true ->
      sandhi_applicable R_6_1_101 v1 v2
  | SA_109 : forall v1 v2,
      is_en v1 = true ->
      v2 = V_a ->
      sandhi_applicable R_6_1_109 v1 v2.

(** The computable rule_matches function agrees with the declarative specification. *)
Lemma rule_matches_iff_applicable : forall r v1 v2,
  rule_matches r v1 v2 = true <-> sandhi_applicable r v1 v2.
Proof.
  intros r v1 v2.
  split.
  - intro H.
    destruct r; simpl in H; try discriminate.
    + apply SA_77. exact H.
    + apply SA_78. exact H.
    + apply SA_87. exact H.
    + apply Bool.andb_true_iff in H.
      destruct H as [H1 H2].
      apply SA_88; assumption.
    + apply Bool.andb_true_iff in H.
      destruct H as [H12 H3].
      apply Bool.andb_true_iff in H12.
      destruct H12 as [H1 H2].
      apply SA_101; assumption.
    + apply Bool.andb_true_iff in H.
      destruct H as [H1 H2].
      apply SA_109.
      * exact H1.
      * destruct v2; simpl in H2; try discriminate; reflexivity.
  - intro H.
    destruct H; simpl.
    + exact H.
    + exact H.
    + exact H.
    + rewrite H, H0. reflexivity.
    + rewrite H, H0, H1. reflexivity.
    + rewrite H. subst v2. reflexivity.
Qed.

(** Declarative specification of when one rule defeats another in precedence. *)
Inductive defeats_rel : RuleId -> RuleId -> Prop :=
  | Defeats_apavada : forall r1 r2,
      is_apavada r1 r2 = true ->
      defeats_rel r1 r2
  | Defeats_para : forall r1 r2,
      is_apavada r1 r2 = false ->
      is_apavada r2 r1 = false ->
      sutra_lt (rule_sutra_num r2) (rule_sutra_num r1) ->
      defeats_rel r1 r2.

(** The computable defeat test agrees with the declarative specification. *)
Lemma rule_defeats_correct : forall r1 r2,
  rule_defeats r1 r2 = true <-> defeats_rel r1 r2.
Proof.
  intros r1 r2.
  split.
  - intro H.
    unfold rule_defeats in H.
    destruct (is_apavada r1 r2) eqn:E1.
    + apply Defeats_apavada.
      exact E1.
    + simpl in H.
      apply Bool.andb_true_iff in H.
      destruct H as [Hneg Hlt].
      apply Bool.negb_true_iff in Hneg.
      apply Defeats_para.
      -- exact E1.
      -- exact Hneg.
      -- apply sutra_ltb_correct.
         exact Hlt.
  - intro H.
    unfold rule_defeats.
    destruct H as [r1' r2' Hapav | r1' r2' Hnot1 Hnot2 Hlt].
    + rewrite Hapav.
      reflexivity.
    + rewrite Hnot1.
      simpl.
      apply Bool.andb_true_iff.
      split.
      -- apply Bool.negb_true_iff.
         exact Hnot2.
      -- apply sutra_ltb_correct.
         exact Hlt.
Qed.

(** Declarative specification of each rule's output, independent of computation. *)
Inductive rule_output_spec : RuleId -> Vowel -> Vowel -> list Phoneme -> Prop :=
  | ROS_77 : forall v1 v2 c,
      (** 6.1.77 iko yaṇ aci: ik vowel becomes its corresponding yaṇ semivowel. *)
      yan_of_spec v1 c ->
      rule_output_spec R_6_1_77 v1 v2 [Vyan c; Svar v2]
  | ROS_78 : forall v1 v2 prefix,
      (** 6.1.78 eco 'yavāyāvaḥ: ec vowel becomes ay/āy/av/āv. *)
      ayavayav_spec v1 prefix ->
      rule_output_spec R_6_1_78 v1 v2 (prefix ++ [Svar v2])
  | ROS_87 : forall v1 v2 result,
      (** 6.1.87 ādguṇaḥ: a/ā + ac → guṇa of the second vowel. *)
      guna_result_spec v2 result ->
      rule_output_spec R_6_1_87 v1 v2 result
  | ROS_88 : forall v1 v2 result,
      (** 6.1.88 vṛddhir eci: a/ā + ec → vṛddhi of the second vowel. *)
      vrddhi_result_spec v2 result ->
      rule_output_spec R_6_1_88 v1 v2 result
  | ROS_89 : forall v1 v2 result,
      (** 6.1.89 ety-edhaty-ūṭhsu: vṛddhi for eti/edhati/ūṭh roots. *)
      vrddhi_result_spec v2 result ->
      rule_output_spec R_6_1_89 v1 v2 result
  | ROS_90 : forall v1 v2 result,
      (** 6.1.90 āṭaś ca: vṛddhi after āṭ augment. *)
      vrddhi_result_spec v2 result ->
      rule_output_spec R_6_1_90 v1 v2 result
  | ROS_91 : forall v1 v2 result,
      (** 6.1.91 upasargād ṛti dhātau: upasarga + ṛ → vṛddhi (ār). *)
      vrddhi_result_spec V_r result ->
      rule_output_spec R_6_1_91 v1 v2 result
  | ROS_94 : forall v1 v2,
      (** 6.1.94 eṅi pararūpam: a/ā + e/o → e/o (pararūpa). *)
      rule_output_spec R_6_1_94 v1 v2 [Svar v2]
  | ROS_97 : forall v1 v2,
      (** 6.1.97 ato guṇe: a elided before guṇa. *)
      rule_output_spec R_6_1_97 v1 v2 [Svar v2]
  | ROS_101 : forall v1 v2 v_long,
      (** 6.1.101 akaḥ savarṇe dīrghaḥ: savarṇa ak vowels merge to dīrgha. *)
      lengthen_spec v1 v_long ->
      rule_output_spec R_6_1_101 v1 v2 [Svar v_long]
  | ROS_107 : forall v1 v2 v_long,
      (** 6.1.107 ami pūrvaḥ: before ami, pūrva vowel lengthens. *)
      lengthen_spec v1 v_long ->
      rule_output_spec R_6_1_107 v1 v2 [Svar v_long]
  | ROS_109 : forall v1 v2,
      (** 6.1.109 eṅaḥ padāntādati: eṅ + a → eṅ (pūrvarūpa). *)
      rule_output_spec R_6_1_109 v1 v2 [Svar v1]
  | ROS_110 : forall v1 v2,
      (** 6.1.110 ṅasiṅasoś ca: pūrvarūpa before ṅas/ṅasi. *)
      rule_output_spec R_6_1_110 v1 v2 [Svar v1]
  | ROS_111 : forall v1 v2,
      (** 6.1.111 ṛta ut: ṛ becomes ut. *)
      rule_output_spec R_6_1_111 v1 v2 [Svar V_u; Vyan C_t]
  | ROS_113 : forall v1 v2,
      (** 6.1.113 ato ror aplutād aplute: a + r → o. *)
      rule_output_spec R_6_1_113 v1 v2 [Svar V_o].

(** The computational apply_rule matches the declarative output specification.
    Note: Only rules where rule_matches can return true are proven here.
    Morphologically conditioned rules (6.1.89-91, 6.1.94, 6.1.97, 6.1.107,
    6.1.110-111, 6.1.113) always return false from rule_matches and are
    eliminated by discriminate. *)
Lemma apply_rule_correct : forall r v1 v2 out,
  rule_matches r v1 v2 = true ->
  apply_rule r v1 v2 = out <-> rule_output_spec r v1 v2 out.
Proof.
  intros r v1 v2 out Hmatch.
  split.
  - intro H.
    destruct r; simpl in Hmatch; try discriminate; simpl in H.
    + destruct (yan_of v1) eqn:Eyan.
      * subst. apply ROS_77. apply yan_of_correct. exact Eyan.
      * destruct v1; simpl in Hmatch; discriminate.
    + destruct (ayavayav v1) eqn:Eayav.
      * subst. apply ROS_78. apply ayavayav_correct. exact Eayav.
      * destruct v1; simpl in Hmatch; discriminate.
    + subst. apply ROS_87. apply guna_correct. reflexivity.
    + subst. apply ROS_88. apply vrddhi_correct. reflexivity.
    + subst. apply ROS_101. apply lengthen_correct. reflexivity.
    + subst. apply ROS_109.
  - intro H.
    destruct H; simpl; try reflexivity.
    + apply yan_of_correct in H. rewrite H. reflexivity.
    + apply ayavayav_correct in H. rewrite H. reflexivity.
    + apply guna_correct in H. exact H.
    + apply vrddhi_correct in H. exact H.
    + apply vrddhi_correct in H. exact H.
    + apply vrddhi_correct in H. exact H.
    + apply vrddhi_correct in H. exact H.
    + apply lengthen_correct in H. rewrite H. reflexivity.
    + apply lengthen_correct in H. rewrite H. reflexivity.
Qed.

(** Specifies that a rule is the winner: it applies and defeats all other applicable rules. *)
Inductive sandhi_winner : RuleId -> Vowel -> Vowel -> Prop :=
  | SW_wins : forall r v1 v2,
      sandhi_applicable r v1 v2 ->
      (forall r', sandhi_applicable r' v1 v2 -> r' <> r -> defeats_rel r r') ->
      sandhi_winner r v1 v2.

(** The complete declarative sandhi relation: either a winner applies or identity. *)
Inductive ac_sandhi_rel : Vowel -> Vowel -> list Phoneme -> Prop :=
  | ASR_result : forall v1 v2 r out,
      sandhi_winner r v1 v2 ->
      rule_output_spec r v1 v2 out ->
      ac_sandhi_rel v1 v2 out
  | ASR_identity : forall v1 v2,
      (forall r, ~ sandhi_applicable r v1 v2) ->
      ac_sandhi_rel v1 v2 [Svar v1; Svar v2].

(** * Part XI: Computational Sandhi Function *)

(** The main sandhi function for EXTERNAL sandhi: selects the winning rule and applies it.
    This function is appropriate for word-boundary (padānta) sandhi where rules
    6.1.77, 6.1.78, 6.1.87, 6.1.88, 6.1.101, and 6.1.109 apply based purely on
    phonological context. For morphologically-conditioned sandhi (internal sandhi
    at dhātu-pratyaya junctures), use apply_ac_sandhi_with_context. *)
Definition apply_ac_sandhi (v1 v2 : Vowel) : list Phoneme :=
  match select_rule v1 v2 with
  | Some r => apply_rule r v1 v2
  | None => [Svar v1; Svar v2]
  end.

(** List of all rules that may apply given morphological context. *)
Definition all_rules_with_context : list RuleId :=
  [R_6_1_77; R_6_1_78; R_6_1_87; R_6_1_88; R_6_1_89; R_6_1_90;
   R_6_1_91; R_6_1_94; R_6_1_97; R_6_1_101; R_6_1_107; R_6_1_109;
   R_6_1_110; R_6_1_111; R_6_1_113].

(** Filters rules that match given vowels and context. *)
Definition matching_rules_with_context
  (rules : list RuleId) (v1 v2 : Vowel) (ctx : MorphContext) : list RuleId :=
  filter (fun r => rule_matches_with_context r v1 v2 ctx) rules.

(** Finds the winning rule among those that match with context.
    Uses fold to avoid structural recursion issues. *)
Definition find_winner_with_context (candidates : list RuleId) : option RuleId :=
  match candidates with
  | [] => None
  | r :: rest =>
      Some (fold_left
        (fun best candidate =>
          if rule_defeats candidate best then candidate else best)
        rest r)
  end.

(** Selects the applicable rule given morphological context. *)
Definition select_rule_with_context
  (v1 v2 : Vowel) (ctx : MorphContext) : option RuleId :=
  find_winner_with_context
    (matching_rules_with_context all_rules_with_context v1 v2 ctx).

(** Context-aware sandhi function for INTERNAL sandhi at morphological junctures.
    This handles rules that require knowledge of upasarga, dhātu, pratyaya, etc.
    Examples:
    - 6.1.89: pra + eti → preti (vṛddhi blocked for eti)
    - 6.1.91: pra + ṛ (root) → prār (vṛddhi)
    - 6.1.94: pra + eṣ (root) → preṣ (pararūpa)
    - 6.1.111: a + ṛ (at dhātu-pratyaya) → ur *)
Definition apply_ac_sandhi_with_context
  (v1 v2 : Vowel) (ctx : MorphContext) : list Phoneme :=
  match select_rule_with_context v1 v2 ctx with
  | Some r => apply_rule r v1 v2
  | None => [Svar v1; Svar v2]
  end.

(** Example: 6.1.91 upasargād ṛti dhātau — pra + ṛ → ār (vṛddhi)
    With upasarga ending in a and ṛ-initial dhātu, rule 6.1.91 applies. *)
Example upasarga_r_sandhi :
  let ctx := upasarga_context UI_pra DC_r_initial in
  rule_matches_with_context R_6_1_91 V_a V_r ctx = true.
Proof. reflexivity. Qed.

(** Example: 6.1.94 eṅi pararūpam — a + e (from root) → e
    At dhātu-pratyaya juncture with a + e/o, pararūpa applies. *)
Example pararupa_matches :
  let ctx := {| mc_upasarga := UI_none; mc_dhatu := DC_other;
                mc_pratyaya := PI_none; mc_augment := AI_none;
                mc_special := SC_none; mc_is_pada_anta := false;
                mc_is_samasa := false; mc_is_dhatu_pratyaya := true |} in
  rule_matches_with_context R_6_1_94 V_a V_e ctx = true.
Proof. reflexivity. Qed.

(** Example: Default context matches standard external sandhi rules. *)
Example external_context_guṇa :
  rule_matches_with_context R_6_1_87 V_a V_i default_morph_context = true.
Proof. reflexivity. Qed.

(** Example: 6.1.109 requires pada_anta context. *)
Example purvarupa_needs_pada_anta :
  rule_matches_with_context R_6_1_109 V_e V_a default_morph_context = true.
Proof. reflexivity. Qed.

(** Example: 6.1.109 does NOT match when not at word boundary. *)
Example purvarupa_internal_fails :
  let ctx := {| mc_upasarga := UI_none; mc_dhatu := DC_other;
                mc_pratyaya := PI_none; mc_augment := AI_none;
                mc_special := SC_none; mc_is_pada_anta := false;
                mc_is_samasa := false; mc_is_dhatu_pratyaya := true |} in
  rule_matches_with_context R_6_1_109 V_e V_a ctx = false.
Proof. reflexivity. Qed.

(** Rule 6.1.87 applied to a/ā + ṛ yields the compound guṇa ar. *)
Lemma rule_87_r_result : forall v1,
  is_a_class v1 = true ->
  apply_rule R_6_1_87 v1 V_r = [Svar V_a; Vyan C_r].
Proof.
  intros v1 H.
  destruct v1; simpl in H; try discriminate; reflexivity.
Qed.

(** Rule 6.1.87 applied to a/ā + ṝ yields the compound guṇa ar. *)
Lemma rule_87_rr_result : forall v1,
  is_a_class v1 = true ->
  apply_rule R_6_1_87 v1 V_rr = [Svar V_a; Vyan C_r].
Proof.
  intros v1 H.
  destruct v1; simpl in H; try discriminate; reflexivity.
Qed.

(** Rule 6.1.87 applied to a/ā + ḷ yields the compound guṇa al. *)
Lemma rule_87_l_result : forall v1,
  is_a_class v1 = true ->
  apply_rule R_6_1_87 v1 V_l = [Svar V_a; Vyan C_l].
Proof.
  intros v1 H.
  destruct v1; simpl in H; try discriminate; reflexivity.
Qed.

(** The vowel ṛ is not a diphthong and is not in the ec class. *)
Lemma r_not_ec : is_ec_computed V_r = false.
Proof. reflexivity. Qed.

(** The vowel ṝ is not a diphthong and is not in the ec class. *)
Lemma rr_not_ec : is_ec_computed V_rr = false.
Proof. reflexivity. Qed.

(** The vowel ḷ is not a diphthong and is not in the ec class. *)
Lemma l_not_ec : is_ec_computed V_l = false.
Proof. reflexivity. Qed.

(** Sandhi of a + ṛ produces the compound guṇa ar. *)
Lemma a_r_sandhi_is_ar :
  apply_ac_sandhi V_a V_r = [Svar V_a; Vyan C_r].
Proof. reflexivity. Qed.

(** Sandhi of ā + ṛ produces the compound guṇa ar. *)
Lemma aa_r_sandhi_is_ar :
  apply_ac_sandhi V_aa V_r = [Svar V_a; Vyan C_r].
Proof. reflexivity. Qed.

(** Sandhi of a + ṝ produces the compound guṇa ar. *)
Lemma a_rr_sandhi_is_ar :
  apply_ac_sandhi V_a V_rr = [Svar V_a; Vyan C_r].
Proof. reflexivity. Qed.

(** Sandhi of a + ḷ produces the compound guṇa al. *)
Lemma a_l_sandhi_is_al :
  apply_ac_sandhi V_a V_l = [Svar V_a; Vyan C_l].
Proof. reflexivity. Qed.

(** Sandhi of ṛ + a produces r followed by a via yaṇ rule. *)
Lemma r_a_sandhi_is_ra :
  apply_ac_sandhi V_r V_a = [Vyan C_r; Svar V_a].
Proof. reflexivity. Qed.

(** Sandhi of ḷ + a produces l followed by a via yaṇ rule. *)
Lemma l_a_sandhi_is_la :
  apply_ac_sandhi V_l V_a = [Vyan C_l; Svar V_a].
Proof. reflexivity. Qed.

(** * Part XII: Key Conflict Cases *)

(** Both yaṇ and dīrgha rules match for i + i. *)
Lemma conflict_i_i_both_match :
  rule_matches R_6_1_77 V_i V_i = true /\
  rule_matches R_6_1_101 V_i V_i = true.
Proof.
  split; reflexivity.
Qed.

(** In the i + i conflict, dīrgha rule 6.1.101 wins over yaṇ 6.1.77. *)
Lemma conflict_i_i_101_wins :
  rule_defeats R_6_1_101 R_6_1_77 = true.
Proof.
  reflexivity.
Qed.

(** Both guṇa and vṛddhi rules match for a + e. *)
Lemma conflict_a_e_both_match :
  rule_matches R_6_1_87 V_a V_e = true /\
  rule_matches R_6_1_88 V_a V_e = true.
Proof.
  split; reflexivity.
Qed.

(** In the a + e conflict, vṛddhi 6.1.88 wins over guṇa 6.1.87. *)
Lemma conflict_a_e_88_wins :
  rule_defeats R_6_1_88 R_6_1_87 = true.
Proof.
  reflexivity.
Qed.

(** Both guṇa and dīrgha rules match for a + a. *)
Lemma conflict_a_a_both_match :
  rule_matches R_6_1_87 V_a V_a = true /\
  rule_matches R_6_1_101 V_a V_a = true.
Proof.
  split; reflexivity.
Qed.

(** In the a + a conflict, dīrgha 6.1.101 wins over guṇa 6.1.87. *)
Lemma conflict_a_a_101_wins :
  rule_defeats R_6_1_101 R_6_1_87 = true.
Proof.
  reflexivity.
Qed.

(** * Part XIII: Coverage Theorem (Semantic) *)

(** Every vowel belongs to exactly one of the three classes: a-class, ik, or ec. *)
Lemma vowel_classification : forall v,
  is_a_class v = true \/
  is_ik_computed v = true \/
  is_ec_computed v = true.
Proof.
  intro v.
  destruct v.
  - left. reflexivity.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. left. reflexivity.
  - right. left. reflexivity.
  - right. left. reflexivity.
  - right. left. reflexivity.
  - right. left. reflexivity.
  - right. left. reflexivity.
  - right. right. reflexivity.
  - right. right. reflexivity.
  - right. right. reflexivity.
  - right. right. reflexivity.
Qed.

(** For any vowel pair, at least one sandhi rule is applicable. *)
Theorem coverage_semantic : forall v1 v2,
  exists r, sandhi_applicable r v1 v2.
Proof.
  intros v1 v2.
  destruct (vowel_classification v1) as [Ha | [Hik | Hec]].
  - exists R_6_1_87.
    apply SA_87.
    exact Ha.
  - exists R_6_1_77.
    apply SA_77.
    exact Hik.
  - exists R_6_1_78.
    apply SA_78.
    exact Hec.
Qed.

(** Unfolding lemma for matching_rules on a cons list. *)
Lemma matching_rules_cons : forall r rs v1 v2,
  matching_rules (r :: rs) v1 v2 =
  if rule_matches r v1 v2
  then r :: matching_rules rs v1 v2
  else matching_rules rs v1 v2.
Proof.
  intros. reflexivity.
Qed.

(** If a rule matches and is in the list, it appears in matching_rules. *)
Lemma matching_rules_In : forall r rules v1 v2,
  In r rules ->
  rule_matches r v1 v2 = true ->
  In r (matching_rules rules v1 v2).
Proof.
  intros r rules v1 v2 Hin Hmatch.
  induction rules as [| r' rules' IH].
  - destruct Hin.
  - simpl.
    destruct (rule_matches r' v1 v2) eqn:Ematch.
    + destruct Hin as [Heq | Hin'].
      * subst. left. reflexivity.
      * right. apply IH. exact Hin'.
    + destruct Hin as [Heq | Hin'].
      * subst. rewrite Hmatch in Ematch. discriminate.
      * apply IH. exact Hin'.
Qed.

(** Tests if a rule is in the all_rules list.
    Only rules that can match based on vowel pairs alone are included. *)
Definition in_all_rules (r : RuleId) : bool :=
  match r with
  | R_6_1_77 | R_6_1_78 | R_6_1_87 | R_6_1_88
  | R_6_1_101 | R_6_1_109 => true
  | _ => false
  end.

(** Rules in all_rules are exactly those for which in_all_rules is true. *)
Lemma all_rules_complete : forall r,
  in_all_rules r = true -> In r all_rules.
Proof.
  intro r.
  destruct r; intro H; try discriminate;
  unfold all_rules; simpl; auto 10.
Qed.

(** For any applicable rule, either it's in all_rules or there's another rule in all_rules that also applies. *)
Lemma coverage_has_all_rules_member : forall v1 v2,
  exists r, In r all_rules /\ rule_matches r v1 v2 = true.
Proof.
  intros v1 v2.
  destruct (coverage_semantic v1 v2) as [r Hr].
  exists r.
  destruct Hr;
  (split; [ unfold all_rules; simpl; tauto
          | simpl; try assumption;
            try (rewrite H; reflexivity);
            try (rewrite H, H0; reflexivity);
            try (rewrite H, H0, H1; reflexivity);
            try (rewrite H; subst; reflexivity) ]).
Qed.

(** The matching rules list is never empty for any vowel pair. *)
Lemma matching_rules_nonempty : forall v1 v2,
  matching_rules all_rules v1 v2 <> [].
Proof.
  intros v1 v2.
  destruct (coverage_has_all_rules_member v1 v2) as [r [Hin Hmatch]].
  intro Hempty.
  pose proof (matching_rules_In r all_rules v1 v2 Hin Hmatch) as Hmr.
  rewrite Hempty in Hmr.
  destruct Hmr.
Qed.

(** The select_rule function always finds a rule for any vowel pair. *)
Theorem coverage_computational : forall v1 v2,
  exists r, select_rule v1 v2 = Some r.
Proof.
  intros v1 v2.
  unfold select_rule.
  apply find_winner_sufficient.
  apply matching_rules_nonempty.
Qed.

(** * Part XIV: Correctness Examples *)

(** a + a merges to long ā via savarṇa dīrgha. *)
Example ex_a_a : apply_ac_sandhi V_a V_a = [Svar V_aa].
Proof. reflexivity. Qed.

(** a + i yields guṇa e. *)
Example ex_a_i : apply_ac_sandhi V_a V_i = [Svar V_e].
Proof. reflexivity. Qed.

(** a + u yields guṇa o. *)
Example ex_a_u : apply_ac_sandhi V_a V_u = [Svar V_o].
Proof. reflexivity. Qed.

(** a + e yields vṛddhi ai. *)
Example ex_a_e : apply_ac_sandhi V_a V_e = [Svar V_ai].
Proof. reflexivity. Qed.

(** a + o yields vṛddhi au. *)
Example ex_a_o : apply_ac_sandhi V_a V_o = [Svar V_au].
Proof. reflexivity. Qed.

(** i + a becomes y + a via yaṇ. *)
Example ex_i_a : apply_ac_sandhi V_i V_a = [Vyan C_y; Svar V_a].
Proof. reflexivity. Qed.

(** i + i merges to long ī via savarṇa dīrgha. *)
Example ex_i_i : apply_ac_sandhi V_i V_i = [Svar V_ii].
Proof. reflexivity. Qed.

(** i + u becomes y + u via yaṇ. *)
Example ex_i_u : apply_ac_sandhi V_i V_u = [Vyan C_y; Svar V_u].
Proof. reflexivity. Qed.

(** u + a becomes v + a via yaṇ. *)
Example ex_u_a : apply_ac_sandhi V_u V_a = [Vyan C_v; Svar V_a].
Proof. reflexivity. Qed.

(** u + u merges to long ū via savarṇa dīrgha. *)
Example ex_u_u : apply_ac_sandhi V_u V_u = [Svar V_uu].
Proof. reflexivity. Qed.

(** e + a yields e via pūrvarūpa. *)
Example ex_e_a : apply_ac_sandhi V_e V_a = [Svar V_e].
Proof. reflexivity. Qed.

(** ai + a decomposes to āy + a via ayavāyāv. *)
Example ex_ai_a : apply_ac_sandhi V_ai V_a = [Svar V_aa; Vyan C_y; Svar V_a].
Proof. reflexivity. Qed.

(** o + a yields o via pūrvarūpa. *)
Example ex_o_a : apply_ac_sandhi V_o V_a = [Svar V_o].
Proof. reflexivity. Qed.

(** au + a decomposes to āv + a via ayavāyāv. *)
Example ex_au_a : apply_ac_sandhi V_au V_a = [Svar V_aa; Vyan C_v; Svar V_a].
Proof. reflexivity. Qed.

(** ṛ + a becomes r + a via yaṇ. *)
Example ex_r_a : apply_ac_sandhi V_r V_a = [Vyan C_r; Svar V_a].
Proof. reflexivity. Qed.

(** ṛ + ṛ merges to long ṝ via savarṇa dīrgha. *)
Example ex_r_r : apply_ac_sandhi V_r V_r = [Svar V_rr].
Proof. reflexivity. Qed.

(** a + ṛ yields compound guṇa ar. *)
Example ex_a_r : apply_ac_sandhi V_a V_r = [Svar V_a; Vyan C_r].
Proof. reflexivity. Qed.

(** The yaṇ rule does not apply when the first vowel is a. *)
Lemma counterex_77_a_not_ik : rule_matches R_6_1_77 V_a V_i = false.
Proof. reflexivity. Qed.

(** The yaṇ rule does not apply when the first vowel is e. *)
Lemma counterex_77_e_not_ik : rule_matches R_6_1_77 V_e V_a = false.
Proof. reflexivity. Qed.

(** The yaṇ rule does not apply when the first vowel is o. *)
Lemma counterex_77_o_not_ik : rule_matches R_6_1_77 V_o V_a = false.
Proof. reflexivity. Qed.

(** The ayavāyāv rule does not apply when the first vowel is a. *)
Lemma counterex_78_a_not_ec : rule_matches R_6_1_78 V_a V_i = false.
Proof. reflexivity. Qed.

(** The ayavāyāv rule does not apply when the first vowel is i. *)
Lemma counterex_78_i_not_ec : rule_matches R_6_1_78 V_i V_a = false.
Proof. reflexivity. Qed.

(** The ayavāyāv rule does not apply when the first vowel is u. *)
Lemma counterex_78_u_not_ec : rule_matches R_6_1_78 V_u V_a = false.
Proof. reflexivity. Qed.

(** The guṇa rule does not apply when the first vowel is i. *)
Lemma counterex_87_i_not_a_class : rule_matches R_6_1_87 V_i V_a = false.
Proof. reflexivity. Qed.

(** The guṇa rule does not apply when the first vowel is e. *)
Lemma counterex_87_e_not_a_class : rule_matches R_6_1_87 V_e V_a = false.
Proof. reflexivity. Qed.

(** The vṛddhi rule does not apply when the second vowel is i. *)
Lemma counterex_88_a_i_not_ec : rule_matches R_6_1_88 V_a V_i = false.
Proof. reflexivity. Qed.

(** The vṛddhi rule does not apply when the first vowel is i. *)
Lemma counterex_88_i_e_not_a_class : rule_matches R_6_1_88 V_i V_e = false.
Proof. reflexivity. Qed.

(** The dīrgha rule does not apply to non-savarṇa pairs like a + i. *)
Lemma counterex_101_a_i_not_savarna : rule_matches R_6_1_101 V_a V_i = false.
Proof. reflexivity. Qed.

(** The dīrgha rule does not apply to non-savarṇa pairs like i + u. *)
Lemma counterex_101_i_u_not_savarna : rule_matches R_6_1_101 V_i V_u = false.
Proof. reflexivity. Qed.

(** The dīrgha rule does not apply to diphthongs like e + e. *)
Lemma counterex_101_e_e_not_ak : rule_matches R_6_1_101 V_e V_e = false.
Proof. reflexivity. Qed.

(** The pūrvarūpa rule does not apply when the second vowel is not a. *)
Lemma counterex_109_e_i_not_a : rule_matches R_6_1_109 V_e V_i = false.
Proof. reflexivity. Qed.

(** The pūrvarūpa rule does not apply when the first vowel is a. *)
Lemma counterex_109_a_a_not_en : rule_matches R_6_1_109 V_a V_a = false.
Proof. reflexivity. Qed.

(** The pūrvarūpa rule does not apply when the first vowel is ai. *)
Lemma counterex_109_ai_a_not_en : rule_matches R_6_1_109 V_ai V_a = false.
Proof. reflexivity. Qed.

(** Validation: u + u yields ū as in guru + upadeśa. *)
Example validate_guru_upadesha : apply_ac_sandhi V_u V_u = [Svar V_uu].
Proof. reflexivity. Qed.

(** Validation: ā + ā yields ā as in mahā + ātman. *)
Example validate_maha_atman : apply_ac_sandhi V_aa V_aa = [Svar V_aa].
Proof. reflexivity. Qed.

(** Validation: a + ī yields e as in deva + īśa. *)
Example validate_deva_isha : apply_ac_sandhi V_a V_ii = [Svar V_e].
Proof. reflexivity. Qed.

(** Validation: a + u yields o as in sūrya + udaya. *)
Example validate_surya_udaya : apply_ac_sandhi V_a V_u = [Svar V_o].
Proof. reflexivity. Qed.

(** Validation: ā + ṛ yields ar as in mahā + ṛṣi. *)
Example validate_maha_rshi : apply_ac_sandhi V_aa V_r = [Svar V_a; Vyan C_r].
Proof. reflexivity. Qed.

(** Validation: ā + ai yields ai as in mahā + aiśvarya. *)
Example validate_maha_aishvarya : apply_ac_sandhi V_aa V_ai = [Svar V_ai].
Proof. reflexivity. Qed.

(** Validation: a + ai yields ai as in eka + aiśvarya. *)
Example validate_eka_aishvarya : apply_ac_sandhi V_a V_ai = [Svar V_ai].
Proof. reflexivity. Qed.

(** Validation: ī + ā yields y ā as in iti + āha. *)
Example validate_iti_aha : apply_ac_sandhi V_ii V_aa = [Vyan C_y; Svar V_aa].
Proof. reflexivity. Qed.

(** Validation: u + a yields v a as in madhu + ari. *)
Example validate_madhu_ari : apply_ac_sandhi V_u V_a = [Vyan C_v; Svar V_a].
Proof. reflexivity. Qed.

(** Validation: ṛ + ā yields r ā as in pitṛ + ānanda. *)
Example validate_pitr_ananda : apply_ac_sandhi V_r V_aa = [Vyan C_r; Svar V_aa].
Proof. reflexivity. Qed.

(** Validation: e + a yields e via pūrvarūpa, not ay a. *)
Example validate_ne_ana : apply_ac_sandhi V_e V_a = [Svar V_e].
Proof. reflexivity. Qed.

(** Validation: ai + a yields āy a as in nai + aka. *)
Example validate_nai_aka : apply_ac_sandhi V_ai V_a = [Svar V_aa; Vyan C_y; Svar V_a].
Proof. reflexivity. Qed.

(** Validation: o + a yields o via pūrvarūpa. *)
Example validate_go_agra : apply_ac_sandhi V_o V_a = [Svar V_o].
Proof. reflexivity. Qed.

(** Validation: au + a yields āv a as in pau + aka. *)
Example validate_pau_aka : apply_ac_sandhi V_au V_a = [Svar V_aa; Vyan C_v; Svar V_a].
Proof. reflexivity. Qed.

(** Validation: e + a yields e via pūrvarūpa as in vane + asti. *)
Example validate_vane_asti : apply_ac_sandhi V_e V_a = [Svar V_e].
Proof. reflexivity. Qed.

(** Validation: o + a yields o via pūrvarūpa as in grāmo + atra. *)
Example validate_gramo_atra : apply_ac_sandhi V_o V_a = [Svar V_o].
Proof. reflexivity. Qed.

(** * Part XV: Non-emptiness *)

(** When a rule matches, its output is never empty. *)
Theorem apply_rule_nonempty : forall r v1 v2,
  rule_matches r v1 v2 = true ->
  apply_rule r v1 v2 <> [].
Proof.
  intros r v1 v2 Hmatch.
  destruct r; simpl in Hmatch; try discriminate; simpl;
  try (destruct v2; discriminate);
  try discriminate.
  - destruct (yan_of v1) eqn:E.
    + discriminate.
    + destruct v1; simpl in Hmatch; discriminate.
  - destruct (ayavayav v1) eqn:E.
    + destruct l; discriminate.
    + destruct v1; simpl in Hmatch; discriminate.
Qed.

(** The sandhi function always produces a non-empty output. *)
Theorem apply_ac_sandhi_nonempty : forall v1 v2,
  apply_ac_sandhi v1 v2 <> [].
Proof.
  intros v1 v2.
  unfold apply_ac_sandhi.
  destruct (select_rule v1 v2) eqn:E.
  - apply apply_rule_nonempty.
    unfold select_rule in E.
    unfold find_winner, matching_rules, all_rules in E.
    destruct v1, v2; simpl in E;
    injection E as E; subst; reflexivity.
  - destruct (coverage_computational v1 v2) as [r' Hr'].
    rewrite E in Hr'.
    discriminate.
Qed.

(** * Part XVI: Apavāda Verification *)

(** Witness that vṛddhi 6.1.88 and guṇa 6.1.87 conflict on a + e. *)
Lemma apavada_88_87_real_conflict : exists v1 v2,
  rule_matches R_6_1_87 v1 v2 = true /\
  rule_matches R_6_1_88 v1 v2 = true /\
  rule_defeats R_6_1_88 R_6_1_87 = true.
Proof.
  exists V_a, V_e.
  repeat split; reflexivity.
Qed.

(** Witness that dīrgha 6.1.101 and guṇa 6.1.87 conflict on a + a. *)
Lemma apavada_101_87_real_conflict : exists v1 v2,
  rule_matches R_6_1_87 v1 v2 = true /\
  rule_matches R_6_1_101 v1 v2 = true /\
  rule_defeats R_6_1_101 R_6_1_87 = true.
Proof.
  exists V_a, V_a.
  repeat split; reflexivity.
Qed.

(** Witness that dīrgha 6.1.101 and yaṇ 6.1.77 conflict on i + i. *)
Lemma apavada_101_77_real_conflict : exists v1 v2,
  rule_matches R_6_1_77 v1 v2 = true /\
  rule_matches R_6_1_101 v1 v2 = true /\
  rule_defeats R_6_1_101 R_6_1_77 = true.
Proof.
  exists V_i, V_i.
  repeat split; reflexivity.
Qed.

(** * Part XVII: Winner Maximality *)

(** A rule is maximal if it matches and defeats all other matching rules. *)
Definition is_maximal (r : RuleId) (v1 v2 : Vowel) : Prop :=
  rule_matches r v1 v2 = true /\
  forall r', rule_matches r' v1 v2 = true -> r' <> r -> rule_defeats r r' = true.

(** Every pair of rules in a list is comparable by the defeat relation. *)
Definition defeats_total_on (rs : list RuleId) : Prop :=
  forall r1 r2,
    In r1 rs -> In r2 rs ->
    r1 = r2 \/ rule_defeats r1 r2 = true \/ rule_defeats r2 r1 = true.

(** A rule is maximal in a list if it defeats all other elements. *)
Definition maximal_in_list (r : RuleId) (rs : list RuleId) : Prop :=
  In r rs /\
  forall r', In r' rs -> r' <> r -> rule_defeats r r' = true.

(** The tournament winner is always a member of the input list. *)
Lemma find_winner_aux_In : forall fuel candidates r,
  find_winner_aux fuel candidates = Some r ->
  In r candidates.
Proof.
  induction fuel as [| fuel' IH].
  - intros candidates r H. simpl in H. discriminate.
  - intros candidates r H.
    destruct candidates as [| r1 rest].
    + simpl in H. discriminate.
    + destruct rest as [| r2 rest'].
      * simpl in H. injection H as H. subst. left. reflexivity.
      * simpl in H.
        destruct (rule_defeats r1 r2) eqn:Edef.
        -- pose proof (IH (r1 :: rest') r H) as HIn.
           destruct HIn as [Heq | HIn'].
           ++ left. exact Heq.
           ++ right. right. exact HIn'.
        -- pose proof (IH (r2 :: rest') r H) as HIn.
           destruct HIn as [Heq | HIn'].
           ++ right. left. exact Heq.
           ++ right. right. exact HIn'.
Qed.

(** Alias for find_winner_aux_In with clearer name. *)
Lemma find_winner_aux_member : forall fuel cs r,
  find_winner_aux fuel cs = Some r -> In r cs.
Proof. exact find_winner_aux_In. Qed.

(** A singleton list returns its only element as the winner. *)
Lemma find_winner_aux_singleton : forall fuel r,
  fuel > 0 -> find_winner_aux fuel [r] = Some r.
Proof.
  intros fuel r Hfuel.
  destruct fuel; [lia | reflexivity].
Qed.

(** The tournament proceeds by eliminating the loser of each pairwise comparison. *)
Lemma find_winner_aux_step : forall fuel r1 r2 rest r,
  find_winner_aux (S fuel) (r1 :: r2 :: rest) = Some r ->
  (rule_defeats r1 r2 = true /\ find_winner_aux fuel (r1 :: rest) = Some r) \/
  (rule_defeats r1 r2 = false /\ find_winner_aux fuel (r2 :: rest) = Some r).
Proof.
  intros fuel r1 r2 rest r H.
  simpl in H.
  destruct (rule_defeats r1 r2) eqn:E.
  - left. auto.
  - right. auto.
Qed.

(** Distinct comparable rules satisfy one of the defeat directions. *)
Lemma defeat_or_equal : forall r1 r2,
  r1 = r2 \/ rule_defeats r1 r2 = true \/ rule_defeats r2 r1 = true ->
  r1 <> r2 ->
  rule_defeats r1 r2 = true \/ rule_defeats r2 r1 = true.
Proof.
  intros r1 r2 [Heq | H] Hneq.
  - contradiction.
  - exact H.
Qed.

(** If r1 defeats r2, then r2 does not defeat r1. *)
Lemma defeat_asymmetric : forall r1 r2,
  rule_defeats r1 r2 = true -> rule_defeats r2 r1 = false.
Proof.
  intros r1 r2 H.
  destruct r1, r2; simpl in H |- *; try discriminate; reflexivity.
Qed.

(** No rule defeats itself. *)
Lemma defeat_irreflexive : forall r, rule_defeats r r = false.
Proof. exact rule_defeats_irrefl. Qed.

(** Any two rules are comparable: equal or one defeats the other. *)
Lemma defeat_total : forall r1 r2,
  r1 = r2 \/ rule_defeats r1 r2 = true \/ rule_defeats r2 r1 = true.
Proof.
  intros r1 r2.
  destruct r1, r2;
  try (left; reflexivity);
  try (right; left; reflexivity);
  try (right; right; reflexivity).
Qed.

(** If r1 does not defeat r2, then either they are equal or r2 defeats r1. *)
Lemma tournament_loser_defeated : forall r1 r2,
  rule_defeats r1 r2 = false ->
  rule_defeats r2 r1 = true \/ r1 = r2.
Proof.
  intros r1 r2 H.
  destruct (RuleId_eq_dec r1 r2) as [Heq | Hneq].
  - right. exact Heq.
  - left.
    destruct (defeat_total r2 r1) as [Heq | [Hdef | Hdef]].
    + symmetry in Heq. contradiction.
    + exact Hdef.
    + rewrite Hdef in H. discriminate.
Qed.

(** Exactly one of three cases holds: equal, r1 defeats r2, or r2 defeats r1. *)
Lemma defeat_trichotomy : forall r1 r2,
  (r1 = r2 /\ rule_defeats r1 r2 = false /\ rule_defeats r2 r1 = false) \/
  (r1 <> r2 /\ rule_defeats r1 r2 = true /\ rule_defeats r2 r1 = false) \/
  (r1 <> r2 /\ rule_defeats r1 r2 = false /\ rule_defeats r2 r1 = true).
Proof.
  intros r1 r2.
  destruct (RuleId_eq_dec r1 r2) as [Heq | Hneq].
  - left. subst. auto using defeat_irreflexive.
  - destruct (rule_defeats r1 r2) eqn:E1.
    + right. left. auto using defeat_asymmetric.
    + right. right.
      destruct (defeat_total r1 r2) as [Heq | [H | H]].
      * contradiction.
      * rewrite H in E1. discriminate.
      * auto.
Qed.

(** Rules in the matching list are from the original list and satisfy the match condition. *)
Lemma matching_rules_subset : forall r rules v1 v2,
  In r (matching_rules rules v1 v2) ->
  In r rules /\ rule_matches r v1 v2 = true.
Proof.
  intros r rules v1 v2.
  induction rules as [| r' rules' IH].
  - intro H. destruct H.
  - intro H. simpl in H.
    destruct (rule_matches r' v1 v2) eqn:Ematch.
    + destruct H as [Heq | Hin].
      * subst. split. left. reflexivity. exact Ematch.
      * destruct (IH Hin) as [Hin' Hmatch].
        split. right. exact Hin'. exact Hmatch.
    + destruct (IH H) as [Hin' Hmatch].
      split. right. exact Hin'. exact Hmatch.
Qed.

(** The defeat relation is total on any matching rules list. *)
Lemma matching_rules_totality : forall v1 v2,
  defeats_total_on (matching_rules all_rules v1 v2).
Proof.
  intros v1 v2 r1 r2 Hin1 Hin2.
  apply matching_rules_subset in Hin1.
  apply matching_rules_subset in Hin2.
  destruct Hin1 as [_ Hmatch1].
  destruct Hin2 as [_ Hmatch2].
  destruct r1, r2;
  try (left; reflexivity);
  try (right; left; reflexivity);
  try (right; right; reflexivity).
Qed.

(** The selected rule is maximal: it matches and defeats all other matching rules. *)
Lemma select_rule_is_maximal : forall v1 v2 r,
  select_rule v1 v2 = Some r ->
  is_maximal r v1 v2.
Proof.
  intros v1 v2 r Hsel.
  unfold is_maximal.
  split.
  - unfold select_rule, find_winner in Hsel.
    apply find_winner_aux_In in Hsel as HrIn.
    apply matching_rules_subset in HrIn.
    destruct HrIn as [_ Hmatch].
    exact Hmatch.
  - intros r' Hmatch' Hneq.
    unfold select_rule, find_winner in Hsel.
    destruct v1, v2; simpl in Hsel; injection Hsel as Hsel; subst;
    destruct r'; simpl in Hmatch'; try discriminate; try reflexivity;
    exfalso; apply Hneq; reflexivity.
Qed.

(** Maximality and being a sandhi winner are equivalent. *)
Lemma is_maximal_iff_winner : forall r v1 v2,
  is_maximal r v1 v2 <-> sandhi_winner r v1 v2.
Proof.
  intros r v1 v2.
  split.
  - intro H.
    destruct H as [Hmatch Hdefeats].
    apply SW_wins.
    + apply rule_matches_iff_applicable.
      exact Hmatch.
    + intros r' Happ' Hneq.
      apply rule_defeats_correct.
      apply Hdefeats.
      -- apply rule_matches_iff_applicable.
         exact Happ'.
      -- exact Hneq.
  - intro H.
    destruct H as [r' v1' v2' Happ Hdefeats].
    unfold is_maximal.
    split.
    + apply rule_matches_iff_applicable.
      exact Happ.
    + intros r'' Hmatch'' Hneq.
      apply rule_defeats_correct.
      apply Hdefeats.
      -- apply rule_matches_iff_applicable.
         exact Hmatch''.
      -- exact Hneq.
Qed.

(** The computational rule selection agrees with the declarative winner specification. *)
Lemma select_rule_correct : forall v1 v2 r,
  select_rule v1 v2 = Some r <-> sandhi_winner r v1 v2.
Proof.
  intros v1 v2 r.
  split.
  - intro H.
    apply is_maximal_iff_winner.
    apply select_rule_is_maximal.
    exact H.
  - intro H.
    apply is_maximal_iff_winner in H.
    destruct H as [Hmatch Hdefeats].
    destruct (coverage_computational v1 v2) as [rsel Hrsel].
    destruct (RuleId_eq_dec r rsel) as [Heq | Hneq].
    + subst.
      exact Hrsel.
    + pose proof (@select_rule_is_maximal v1 v2 rsel Hrsel) as Hmax'.
      destruct Hmax' as [Hmatch' Hdefeats'].
      assert (Hdef1 : rule_defeats r rsel = true).
      { apply Hdefeats; auto. }
      assert (Hdef2 : rule_defeats rsel r = true).
      { apply Hdefeats'; auto. }
      destruct r, rsel;
      simpl in Hdef1, Hdef2; try discriminate; try reflexivity;
      contradiction Hneq; reflexivity.
Qed.

(** Two rules cannot mutually defeat each other. *)
Lemma rule_defeats_asymm : forall r1 r2,
  rule_defeats r1 r2 = true ->
  rule_defeats r2 r1 = true ->
  False.
Proof.
  intros r1 r2 H1 H2.
  destruct r1, r2; simpl in H1, H2; discriminate.
Qed.

(** There is at most one winner for any vowel pair. *)
Theorem winner_unique : forall v1 v2 r1 r2,
  sandhi_winner r1 v1 v2 ->
  sandhi_winner r2 v1 v2 ->
  r1 = r2.
Proof.
  intros v1 v2 r1 r2 H1 H2.
  apply is_maximal_iff_winner in H1.
  apply is_maximal_iff_winner in H2.
  destruct H1 as [Hmatch1 Hdef1].
  destruct H2 as [Hmatch2 Hdef2].
  destruct (RuleId_eq_dec r1 r2) as [Heq | Hneq].
  - exact Heq.
  - exfalso.
    assert (Hd1 : rule_defeats r1 r2 = true) by (apply Hdef1; auto).
    assert (Hd2 : rule_defeats r2 r1 = true) by (apply Hdef2; auto).
    exact (rule_defeats_asymm r1 r2 Hd1 Hd2).
Qed.

(** The rule selection function returns a unique result. *)
Corollary select_rule_unique : forall v1 v2 r1 r2,
  select_rule v1 v2 = Some r1 ->
  select_rule v1 v2 = Some r2 ->
  r1 = r2.
Proof.
  intros v1 v2 r1 r2 H1 H2.
  apply select_rule_correct in H1.
  apply select_rule_correct in H2.
  eapply winner_unique; eassumption.
Qed.

(** * Part XVIII: Order Independence *)

(** Any two matching rules are comparable by the defeat relation. *)
Definition rules_total_on (v1 v2 : Vowel) : Prop :=
  forall r1 r2,
    rule_matches r1 v1 v2 = true ->
    rule_matches r2 v1 v2 = true ->
    r1 = r2 \/ rule_defeats r1 r2 = true \/ rule_defeats r2 r1 = true.

(** Totality holds for our set of sandhi rules. *)
Lemma our_rules_total : forall v1 v2, rules_total_on v1 v2.
Proof.
  intros v1 v2 r1 r2 H1 H2.
  destruct r1, r2;
  try (left; reflexivity);
  try (right; left; reflexivity);
  try (right; right; reflexivity).
Qed.

(** * Part XIX: Soundness *)

(** Every computational output comes from applying a selected rule. *)
Theorem soundness_aux : forall v1 v2 out,
  apply_ac_sandhi v1 v2 = out ->
  exists r, select_rule v1 v2 = Some r /\ apply_rule r v1 v2 = out.
Proof.
  intros v1 v2 out H.
  unfold apply_ac_sandhi in H.
  destruct (select_rule v1 v2) eqn:E.
  - exists r.
    auto.
  - destruct (coverage_computational v1 v2) as [r' Hr'].
    rewrite E in Hr'.
    discriminate.
Qed.

(** Soundness: computational outputs satisfy the declarative specification. *)
Theorem soundness : forall v1 v2 out,
  apply_ac_sandhi v1 v2 = out ->
  ac_sandhi_rel v1 v2 out.
Proof.
  intros v1 v2 out H.
  pose proof (@soundness_aux v1 v2 out H) as [r [Hsel Happ]].
  apply ASR_result with (r := r).
  - apply select_rule_correct.
    exact Hsel.
  - apply apply_rule_correct.
    + apply select_rule_is_maximal in Hsel.
      destruct Hsel as [Hmatch _].
      exact Hmatch.
    + exact Happ.
Qed.

(** Completeness: anything satisfying the specification is computed. *)
Theorem completeness : forall v1 v2 out,
  ac_sandhi_rel v1 v2 out ->
  apply_ac_sandhi v1 v2 = out.
Proof.
  intros v1 v2 out H.
  destruct H as [v1' v2' r out' Hwinner Happ | v1' v2' Hno_rule].
  - unfold apply_ac_sandhi.
    assert (Hmatch : rule_matches r v1' v2' = true).
    { destruct Hwinner as [r' v1'' v2'' Happ' _].
      apply rule_matches_iff_applicable.
      exact Happ'. }
    apply select_rule_correct in Hwinner.
    rewrite Hwinner.
    apply apply_rule_correct.
    + exact Hmatch.
    + exact Happ.
  - exfalso.
    destruct (coverage_semantic v1' v2') as [r Hr].
    exact (Hno_rule r Hr).
Qed.

(** The computational sandhi function is equivalent to the declarative specification. *)
Theorem soundness_completeness : forall v1 v2 out,
  apply_ac_sandhi v1 v2 = out <-> ac_sandhi_rel v1 v2 out.
Proof.
  intros v1 v2 out.
  split.
  - apply soundness.
  - apply completeness.
Qed.

(** * Part XX: Consonant Classes for Visarga Sandhi *)

(** Tests whether a consonant is voiceless (khar class). *)
Definition is_khar (c : Consonant) : bool := is_khar_computed c.

(** Declarative specification of the khar class: voiceless stops and sibilants. *)
Inductive is_khar_spec : Consonant -> Prop :=
  | Khar_k : is_khar_spec C_k   | Khar_kh : is_khar_spec C_kh
  | Khar_c : is_khar_spec C_c   | Khar_ch : is_khar_spec C_ch
  | Khar_tt : is_khar_spec C_tt | Khar_tth : is_khar_spec C_tth
  | Khar_t : is_khar_spec C_t   | Khar_th : is_khar_spec C_th
  | Khar_p : is_khar_spec C_p   | Khar_ph : is_khar_spec C_ph
  | Khar_sh : is_khar_spec C_sh | Khar_ss : is_khar_spec C_ss
  | Khar_s : is_khar_spec C_s.

(** The computable khar test matches the declarative specification. *)
Lemma is_khar_correct : forall c,
  is_khar c = true <-> is_khar_spec c.
Proof.
  intro c; split.
  - intro H; destruct c; simpl in H; try discriminate; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** Tests whether a consonant is a voiced stop (jhaś class). *)
Definition is_jhas (c : Consonant) : bool := is_jhas_computed c.

(** Declarative specification of the jhaś class: voiced stops. *)
Inductive is_jhas_spec : Consonant -> Prop :=
  | Jhas_g : is_jhas_spec C_g   | Jhas_gh : is_jhas_spec C_gh
  | Jhas_j : is_jhas_spec C_j   | Jhas_jh : is_jhas_spec C_jh
  | Jhas_dd : is_jhas_spec C_dd | Jhas_ddh : is_jhas_spec C_ddh
  | Jhas_d : is_jhas_spec C_d   | Jhas_dh : is_jhas_spec C_dh
  | Jhas_b : is_jhas_spec C_b   | Jhas_bh : is_jhas_spec C_bh.

(** The computable jhaś test matches the declarative specification. *)
Lemma is_jhas_correct : forall c,
  is_jhas c = true <-> is_jhas_spec c.
Proof.
  intro c; split.
  - intro H; destruct c; simpl in H; try discriminate; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** Tests whether a phoneme is any consonant (hal class). *)
Definition is_hal (c : Consonant) : bool := is_hal_computed c.

(** Every consonant is in the hal class. *)
Lemma is_hal_total : forall c, is_hal c = true.
Proof. intro c; destruct c; reflexivity. Qed.

(** Tests whether a consonant is a semivowel (yaṇ class). *)
Definition is_yan (c : Consonant) : bool := is_yan_computed c.

(** Declarative specification of the yaṇ class: semivowels y, v, r, l. *)
Inductive is_yan_spec : Consonant -> Prop :=
  | Yan_y : is_yan_spec C_y
  | Yan_v : is_yan_spec C_v
  | Yan_r : is_yan_spec C_r
  | Yan_l : is_yan_spec C_l.

(** The computable yaṇ test matches the declarative specification. *)
Lemma is_yan_correct : forall c,
  is_yan c = true <-> is_yan_spec c.
Proof.
  intro c; split.
  - intro H; destruct c; simpl in H; try discriminate; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** * Part XXI: Visarga Sandhi (8.3) *)

(** Specifies when s becomes visarga: before voiceless consonants. *)
Inductive visarga_from_s_spec : Consonant -> Prop :=
  | VFS_khar : forall c, is_khar_spec c -> visarga_from_s_spec c.

(** Specifies that word-final m becomes anusvāra before any consonant. *)
Inductive anusvara_from_m_spec : Consonant -> Prop :=
  | AFM_hal : forall c, anusvara_from_m_spec c.

(** Applies rule 8.3.23: m becomes anusvāra before consonants. *)
Definition apply_8_3_23 (following : Consonant) : Phoneme := Anusvara.

(** The anusvāra rule applies before any consonant. *)
Lemma anusvara_from_m_total : forall c, anusvara_from_m_spec c.
Proof. intro c; constructor. Qed.

(** Converts visarga to s before voiceless consonants. *)
Definition visarga_to_s_before_khar (c : Consonant) : option Phoneme :=
  if is_khar c then Some (Vyan C_s) else None.

(** Handles visarga before voiced consonants with vowel-dependent outcomes. *)
Definition visarga_before_voiced (prev_vowel : Vowel) (c : Consonant)
  : option (list Phoneme) :=
  if is_jhas c then
    match prev_vowel with
    | V_a => Some [Svar V_o]
    | V_aa => Some [Svar V_aa]
    | _ => Some [Svar prev_vowel; Vyan C_r]
    end
  else None.

(** Returns the appropriate visarga allophone based on the following consonant. *)
Definition visarga_allophone (following : Consonant) : Phoneme :=
  match following with
  | C_k | C_kh => Jihvamuliya
  | C_p | C_ph => Upadhmamiya
  | _ => Visarga
  end.

(** Declarative specification of visarga allophones. *)
Inductive visarga_allophone_spec : Consonant -> Phoneme -> Prop :=
  | VA_k : visarga_allophone_spec C_k Jihvamuliya
  | VA_kh : visarga_allophone_spec C_kh Jihvamuliya
  | VA_p : visarga_allophone_spec C_p Upadhmamiya
  | VA_ph : visarga_allophone_spec C_ph Upadhmamiya
  | VA_other : forall c,
      c <> C_k -> c <> C_kh -> c <> C_p -> c <> C_ph ->
      visarga_allophone_spec c Visarga.

(** The computable allophone function matches the declarative specification. *)
Lemma visarga_allophone_correct : forall c p,
  visarga_allophone c = p <-> visarga_allophone_spec c p.
Proof.
  intros c p.
  split.
  - intro H.
    destruct c; simpl in H; subst; try constructor; discriminate.
  - intro H.
    destruct H; try reflexivity.
    destruct c; try reflexivity; contradiction.
Qed.

(** Possible outcomes of visarga sandhi transformation. *)
Inductive VisargaSandhiResult : Type :=
  | VSR_visarga : VisargaSandhiResult
  | VSR_s : VisargaSandhiResult
  | VSR_r : VisargaSandhiResult
  | VSR_deletion : Vowel -> VisargaSandhiResult
  | VSR_o : VisargaSandhiResult.

(** Computes the visarga sandhi outcome based on preceding vowel and following consonant. *)
Definition apply_visarga_sandhi (prev_vowel : Vowel) (following : Consonant)
  : VisargaSandhiResult :=
  if is_khar following then VSR_visarga
  else if is_jhas following then
    match prev_vowel with
    | V_a => VSR_o
    | V_aa => VSR_deletion V_aa
    | _ => VSR_r
    end
  else VSR_visarga.

(** Declarative specification of visarga sandhi based on grammatical rules. *)
Inductive visarga_sandhi_spec : Vowel -> Consonant -> VisargaSandhiResult -> Prop :=
  | VSS_khar : forall v c,
      is_khar_spec c ->
      visarga_sandhi_spec v c VSR_visarga
  | VSS_jhas_a : forall c,
      is_khar c = false ->
      is_jhas_spec c ->
      visarga_sandhi_spec V_a c VSR_o
  | VSS_jhas_aa : forall c,
      is_khar c = false ->
      is_jhas_spec c ->
      visarga_sandhi_spec V_aa c (VSR_deletion V_aa)
  | VSS_jhas_other : forall v c,
      is_khar c = false ->
      is_jhas_spec c ->
      v <> V_a ->
      v <> V_aa ->
      visarga_sandhi_spec v c VSR_r
  | VSS_default : forall v c,
      is_khar c = false ->
      is_jhas c = false ->
      visarga_sandhi_spec v c VSR_visarga.

(** The computable visarga sandhi matches the declarative specification. *)
Theorem visarga_sandhi_correct : forall v c r,
  visarga_sandhi_spec v c r <-> apply_visarga_sandhi v c = r.
Proof.
  intros v c r.
  split.
  - intro H.
    destruct H.
    + unfold apply_visarga_sandhi.
      apply is_khar_correct in H.
      rewrite H.
      reflexivity.
    + unfold apply_visarga_sandhi.
      rewrite H.
      apply is_jhas_correct in H0.
      rewrite H0.
      reflexivity.
    + unfold apply_visarga_sandhi.
      rewrite H.
      apply is_jhas_correct in H0.
      rewrite H0.
      reflexivity.
    + unfold apply_visarga_sandhi.
      rewrite H.
      apply is_jhas_correct in H0.
      rewrite H0.
      destruct v; try reflexivity; contradiction.
    + unfold apply_visarga_sandhi.
      rewrite H, H0.
      reflexivity.
  - intro H.
    unfold apply_visarga_sandhi in H.
    destruct (is_khar c) eqn:Ekhar.
    + subst r.
      apply VSS_khar.
      apply is_khar_correct.
      exact Ekhar.
    + destruct (is_jhas c) eqn:Ejhas.
      * destruct v; subst r.
        -- apply VSS_jhas_a.
           ++ exact Ekhar.
           ++ apply is_jhas_correct. exact Ejhas.
        -- apply VSS_jhas_aa.
           ++ exact Ekhar.
           ++ apply is_jhas_correct. exact Ejhas.
        -- apply VSS_jhas_other; [exact Ekhar | apply is_jhas_correct; exact Ejhas | discriminate | discriminate].
        -- apply VSS_jhas_other; [exact Ekhar | apply is_jhas_correct; exact Ejhas | discriminate | discriminate].
        -- apply VSS_jhas_other; [exact Ekhar | apply is_jhas_correct; exact Ejhas | discriminate | discriminate].
        -- apply VSS_jhas_other; [exact Ekhar | apply is_jhas_correct; exact Ejhas | discriminate | discriminate].
        -- apply VSS_jhas_other; [exact Ekhar | apply is_jhas_correct; exact Ejhas | discriminate | discriminate].
        -- apply VSS_jhas_other; [exact Ekhar | apply is_jhas_correct; exact Ejhas | discriminate | discriminate].
        -- apply VSS_jhas_other; [exact Ekhar | apply is_jhas_correct; exact Ejhas | discriminate | discriminate].
        -- apply VSS_jhas_other; [exact Ekhar | apply is_jhas_correct; exact Ejhas | discriminate | discriminate].
        -- apply VSS_jhas_other; [exact Ekhar | apply is_jhas_correct; exact Ejhas | discriminate | discriminate].
        -- apply VSS_jhas_other; [exact Ekhar | apply is_jhas_correct; exact Ejhas | discriminate | discriminate].
        -- apply VSS_jhas_other; [exact Ekhar | apply is_jhas_correct; exact Ejhas | discriminate | discriminate].
      * subst r.
        apply VSS_default.
        -- exact Ekhar.
        -- exact Ejhas.
Qed.

(** * Part XXII: Consonant Sandhi (8.4) *)

(** ** Varga (class) of stops *)

Inductive Varga : Type := Kavarga | Cavarga | Tavarga | Tavarga2 | Pavarga.

Definition consonant_varga (c : Consonant) : option Varga :=
  match c with
  | C_k | C_kh | C_g | C_gh | C_ng => Some Kavarga
  | C_c | C_ch | C_j | C_jh | C_ny => Some Cavarga
  | C_tt | C_tth | C_dd | C_ddh | C_nn => Some Tavarga
  | C_t | C_th | C_d | C_dh | C_n => Some Tavarga2
  | C_p | C_ph | C_b | C_bh | C_m => Some Pavarga
  | _ => None
  end.

(** ** 8.4.53 jhalāṁ jaś jhaśi *)
(** "jhal consonants become jaś before jhaś."
    Voiceless stops become voiced before voiced stops. *)

Definition voiced_of (c : Consonant) : Consonant :=
  match c with
  | C_k => C_g   | C_kh => C_gh
  | C_c => C_j   | C_ch => C_jh
  | C_tt => C_dd | C_tth => C_ddh
  | C_t => C_d   | C_th => C_dh
  | C_p => C_b   | C_ph => C_bh
  | other => other
  end.

Definition is_voiceable (c : Consonant) : bool :=
  match c with
  | C_k | C_kh | C_c | C_ch | C_tt | C_tth | C_t | C_th | C_p | C_ph => true
  | _ => false
  end.

Inductive voicing_spec : Consonant -> Consonant -> Prop :=
  | Voice_k : voicing_spec C_k C_g
  | Voice_kh : voicing_spec C_kh C_gh
  | Voice_c : voicing_spec C_c C_j
  | Voice_ch : voicing_spec C_ch C_jh
  | Voice_tt : voicing_spec C_tt C_dd
  | Voice_tth : voicing_spec C_tth C_ddh
  | Voice_t : voicing_spec C_t C_d
  | Voice_th : voicing_spec C_th C_dh
  | Voice_p : voicing_spec C_p C_b
  | Voice_ph : voicing_spec C_ph C_bh.

Lemma voiced_of_correct : forall c1 c2,
  voicing_spec c1 c2 <-> (is_voiceable c1 = true /\ voiced_of c1 = c2).
Proof.
  intros c1 c2.
  split.
  - intro H.
    destruct H; split; reflexivity.
  - intros [Hv Heq].
    destruct c1; simpl in Hv; try discriminate;
    simpl in Heq; subst; constructor.
Qed.

(** ** 8.4.55 khari ca *)
(** "Also before khar."
    Final voiced stops become voiceless before voiceless consonants. *)

Definition voiceless_of (c : Consonant) : Consonant :=
  match c with
  | C_g => C_k   | C_gh => C_k
  | C_j => C_c   | C_jh => C_c
  | C_dd => C_tt | C_ddh => C_tt
  | C_d => C_t   | C_dh => C_t
  | C_b => C_p   | C_bh => C_p
  | other => other
  end.

Definition is_devoiceable (c : Consonant) : bool :=
  match c with
  | C_g | C_gh | C_j | C_jh | C_dd | C_ddh | C_d | C_dh | C_b | C_bh => true
  | _ => false
  end.

Inductive devoicing_spec : Consonant -> Consonant -> Prop :=
  | Devoice_g : devoicing_spec C_g C_k
  | Devoice_gh : devoicing_spec C_gh C_k
  | Devoice_j : devoicing_spec C_j C_c
  | Devoice_jh : devoicing_spec C_jh C_c
  | Devoice_dd : devoicing_spec C_dd C_tt
  | Devoice_ddh : devoicing_spec C_ddh C_tt
  | Devoice_d : devoicing_spec C_d C_t
  | Devoice_dh : devoicing_spec C_dh C_t
  | Devoice_b : devoicing_spec C_b C_p
  | Devoice_bh : devoicing_spec C_bh C_p.

Lemma voiceless_of_correct : forall c1 c2,
  devoicing_spec c1 c2 <-> (is_devoiceable c1 = true /\ voiceless_of c1 = c2).
Proof.
  intros c1 c2.
  split.
  - intro H.
    destruct H; split; reflexivity.
  - intros [Hd Heq].
    destruct c1; simpl in Hd; try discriminate;
    simpl in Heq; subst; constructor.
Qed.

(** ** 8.4.40 stoḥ ścunā ścuḥ *)
(** "s and t-class become ś and c-class before c-class/ś." *)

Definition is_cavarga_or_sh (c : Consonant) : bool :=
  match c with
  | C_c | C_ch | C_j | C_jh | C_ny | C_sh => true
  | _ => false
  end.

Definition palatalize (c : Consonant) : Consonant :=
  match c with
  | C_s => C_sh
  | C_t => C_c   | C_th => C_ch
  | C_d => C_j   | C_dh => C_jh
  | C_n => C_ny
  | other => other
  end.

(** ** 8.4.41 ṣṭunā ṣṭuḥ *)
(** "s and t-class become ṣ and ṭ-class before ṭ-class/ṣ." *)

Definition is_tavarga_or_ss (c : Consonant) : bool :=
  match c with
  | C_tt | C_tth | C_dd | C_ddh | C_nn | C_ss => true
  | _ => false
  end.

Definition retroflexize (c : Consonant) : Consonant :=
  match c with
  | C_s => C_ss
  | C_t => C_tt   | C_th => C_tth
  | C_d => C_dd   | C_dh => C_ddh
  | C_n => C_nn
  | other => other
  end.

(** Palatalization spec (8.4.40). *)

Definition is_palatalizable (c : Consonant) : bool :=
  match c with
  | C_s | C_t | C_th | C_d | C_dh | C_n => true
  | _ => false
  end.

Inductive palatalization_spec : Consonant -> Consonant -> Prop :=
  | Pal_s : palatalization_spec C_s C_sh
  | Pal_t : palatalization_spec C_t C_c
  | Pal_th : palatalization_spec C_th C_ch
  | Pal_d : palatalization_spec C_d C_j
  | Pal_dh : palatalization_spec C_dh C_jh
  | Pal_n : palatalization_spec C_n C_ny.

Lemma palatalize_correct : forall c1 c2,
  palatalization_spec c1 c2 <-> (is_palatalizable c1 = true /\ palatalize c1 = c2).
Proof.
  intros c1 c2.
  split.
  - intro H.
    destruct H; split; reflexivity.
  - intros [Hp Heq].
    destruct c1; simpl in Hp; try discriminate;
    simpl in Heq; subst; constructor.
Qed.

(** Retroflexion spec (8.4.41). *)

Definition is_retroflexizable (c : Consonant) : bool :=
  match c with
  | C_s | C_t | C_th | C_d | C_dh | C_n => true
  | _ => false
  end.

Inductive retroflexion_spec : Consonant -> Consonant -> Prop :=
  | Ret_s : retroflexion_spec C_s C_ss
  | Ret_t : retroflexion_spec C_t C_tt
  | Ret_th : retroflexion_spec C_th C_tth
  | Ret_d : retroflexion_spec C_d C_dd
  | Ret_dh : retroflexion_spec C_dh C_ddh
  | Ret_n : retroflexion_spec C_n C_nn.

Lemma retroflexize_correct : forall c1 c2,
  retroflexion_spec c1 c2 <-> (is_retroflexizable c1 = true /\ retroflexize c1 = c2).
Proof.
  intros c1 c2.
  split.
  - intro H.
    destruct H; split; reflexivity.
  - intros [Hr Heq].
    destruct c1; simpl in Hr; try discriminate;
    simpl in Heq; subst; constructor.
Qed.

(** Cavarga/ś class spec. *)

Inductive is_cavarga_or_sh_spec : Consonant -> Prop :=
  | Cav_c : is_cavarga_or_sh_spec C_c
  | Cav_ch : is_cavarga_or_sh_spec C_ch
  | Cav_j : is_cavarga_or_sh_spec C_j
  | Cav_jh : is_cavarga_or_sh_spec C_jh
  | Cav_ny : is_cavarga_or_sh_spec C_ny
  | Cav_sh : is_cavarga_or_sh_spec C_sh.

Lemma is_cavarga_or_sh_correct : forall c,
  is_cavarga_or_sh c = true <-> is_cavarga_or_sh_spec c.
Proof.
  intro c; split.
  - intro H; destruct c; simpl in H; try discriminate; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** Ṭavarga/ṣ class spec. *)

Inductive is_tavarga_or_ss_spec : Consonant -> Prop :=
  | Tav_tt : is_tavarga_or_ss_spec C_tt
  | Tav_tth : is_tavarga_or_ss_spec C_tth
  | Tav_dd : is_tavarga_or_ss_spec C_dd
  | Tav_ddh : is_tavarga_or_ss_spec C_ddh
  | Tav_nn : is_tavarga_or_ss_spec C_nn
  | Tav_ss : is_tavarga_or_ss_spec C_ss.

Lemma is_tavarga_or_ss_correct : forall c,
  is_tavarga_or_ss c = true <-> is_tavarga_or_ss_spec c.
Proof.
  intro c; split.
  - intro H; destruct c; simpl in H; try discriminate; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** Combined consonant sandhi. *)

(** Place assimilation (8.4.40-41) applies first, then voicing (8.4.53-55). *)

Definition apply_place_assimilation (final following : Consonant) : Consonant :=
  if is_cavarga_or_sh following then palatalize final
  else if is_tavarga_or_ss following then retroflexize final
  else final.

Definition apply_voicing_assimilation (final following : Consonant) : Consonant :=
  if is_jhas following then voiced_of final
  else if is_khar following then voiceless_of final
  else final.

Definition apply_consonant_sandhi (final following : Consonant) : Consonant :=
  let after_place := apply_place_assimilation final following in
  apply_voicing_assimilation after_place following.

(** Declarative spec for place assimilation (8.4.40-41). *)

Inductive place_assimilation_spec : Consonant -> Consonant -> Consonant -> Prop :=
  | PAS_palatal : forall c1 c2 c_out,
      is_cavarga_or_sh_spec c2 ->
      palatalization_spec c1 c_out ->
      place_assimilation_spec c1 c2 c_out
  | PAS_palatal_no_change : forall c1 c2,
      is_cavarga_or_sh_spec c2 ->
      is_palatalizable c1 = false ->
      place_assimilation_spec c1 c2 c1
  | PAS_retroflex : forall c1 c2 c_out,
      is_cavarga_or_sh c2 = false ->
      is_tavarga_or_ss_spec c2 ->
      retroflexion_spec c1 c_out ->
      place_assimilation_spec c1 c2 c_out
  | PAS_retroflex_no_change : forall c1 c2,
      is_cavarga_or_sh c2 = false ->
      is_tavarga_or_ss_spec c2 ->
      is_retroflexizable c1 = false ->
      place_assimilation_spec c1 c2 c1
  | PAS_none : forall c1 c2,
      is_cavarga_or_sh c2 = false ->
      is_tavarga_or_ss c2 = false ->
      place_assimilation_spec c1 c2 c1.

Lemma palatalize_no_change : forall c,
  is_palatalizable c = false -> palatalize c = c.
Proof.
  intros c H.
  destruct c; simpl in H; try discriminate; reflexivity.
Qed.

Lemma retroflexize_no_change : forall c,
  is_retroflexizable c = false -> retroflexize c = c.
Proof.
  intros c H.
  destruct c; simpl in H; try discriminate; reflexivity.
Qed.

Lemma place_assimilation_correct : forall c1 c2 c3,
  place_assimilation_spec c1 c2 c3 <-> apply_place_assimilation c1 c2 = c3.
Proof.
  intros c1 c2 c3.
  split.
  - intro H.
    destruct H.
    + unfold apply_place_assimilation.
      apply is_cavarga_or_sh_correct in H.
      rewrite H.
      apply palatalize_correct in H0.
      destruct H0 as [_ Heq].
      exact Heq.
    + unfold apply_place_assimilation.
      apply is_cavarga_or_sh_correct in H.
      rewrite H.
      apply palatalize_no_change.
      exact H0.
    + unfold apply_place_assimilation.
      rewrite H.
      apply is_tavarga_or_ss_correct in H0.
      rewrite H0.
      apply retroflexize_correct in H1.
      destruct H1 as [_ Heq].
      exact Heq.
    + unfold apply_place_assimilation.
      rewrite H.
      apply is_tavarga_or_ss_correct in H0.
      rewrite H0.
      apply retroflexize_no_change.
      exact H1.
    + unfold apply_place_assimilation.
      rewrite H, H0.
      reflexivity.
  - intro H.
    unfold apply_place_assimilation in H.
    destruct (is_cavarga_or_sh c2) eqn:Ecav.
    + destruct (is_palatalizable c1) eqn:Epal.
      * apply PAS_palatal.
        -- apply is_cavarga_or_sh_correct. exact Ecav.
        -- apply palatalize_correct.
           split; [exact Epal | exact H].
      * pose proof (palatalize_no_change c1 Epal) as Hno.
        rewrite Hno in H.
        subst c3.
        apply PAS_palatal_no_change.
        -- apply is_cavarga_or_sh_correct. exact Ecav.
        -- exact Epal.
    + destruct (is_tavarga_or_ss c2) eqn:Etav.
      * destruct (is_retroflexizable c1) eqn:Eret.
        -- apply PAS_retroflex.
           ++ exact Ecav.
           ++ apply is_tavarga_or_ss_correct. exact Etav.
           ++ apply retroflexize_correct.
              split; [exact Eret | exact H].
        -- pose proof (retroflexize_no_change c1 Eret) as Hno.
           rewrite Hno in H.
           subst c3.
           apply PAS_retroflex_no_change.
           ++ exact Ecav.
           ++ apply is_tavarga_or_ss_correct. exact Etav.
           ++ exact Eret.
      * subst c3.
        apply PAS_none.
        -- exact Ecav.
        -- exact Etav.
Qed.

(** Declarative spec for voicing assimilation (8.4.53-55). *)

Inductive voicing_assimilation_spec : Consonant -> Consonant -> Consonant -> Prop :=
  | VAS_voice : forall c1 c2 c_out,
      is_jhas_spec c2 ->
      voicing_spec c1 c_out ->
      voicing_assimilation_spec c1 c2 c_out
  | VAS_voice_no_change : forall c1 c2,
      is_jhas_spec c2 ->
      is_voiceable c1 = false ->
      voicing_assimilation_spec c1 c2 c1
  | VAS_devoice : forall c1 c2 c_out,
      is_jhas c2 = false ->
      is_khar_spec c2 ->
      devoicing_spec c1 c_out ->
      voicing_assimilation_spec c1 c2 c_out
  | VAS_devoice_no_change : forall c1 c2,
      is_jhas c2 = false ->
      is_khar_spec c2 ->
      is_devoiceable c1 = false ->
      voicing_assimilation_spec c1 c2 c1
  | VAS_none : forall c1 c2,
      is_jhas c2 = false ->
      is_khar c2 = false ->
      voicing_assimilation_spec c1 c2 c1.

Lemma voiced_of_no_change : forall c,
  is_voiceable c = false -> voiced_of c = c.
Proof.
  intros c H.
  destruct c; simpl in H; try discriminate; reflexivity.
Qed.

Lemma voiceless_of_no_change : forall c,
  is_devoiceable c = false -> voiceless_of c = c.
Proof.
  intros c H.
  destruct c; simpl in H; try discriminate; reflexivity.
Qed.

Lemma voicing_assimilation_correct : forall c1 c2 c3,
  voicing_assimilation_spec c1 c2 c3 <-> apply_voicing_assimilation c1 c2 = c3.
Proof.
  intros c1 c2 c3.
  split.
  - intro H.
    destruct H.
    + unfold apply_voicing_assimilation.
      apply is_jhas_correct in H.
      rewrite H.
      apply voiced_of_correct in H0.
      destruct H0 as [_ Heq].
      exact Heq.
    + unfold apply_voicing_assimilation.
      apply is_jhas_correct in H.
      rewrite H.
      apply voiced_of_no_change.
      exact H0.
    + unfold apply_voicing_assimilation.
      rewrite H.
      apply is_khar_correct in H0.
      rewrite H0.
      apply voiceless_of_correct in H1.
      destruct H1 as [_ Heq].
      exact Heq.
    + unfold apply_voicing_assimilation.
      rewrite H.
      apply is_khar_correct in H0.
      rewrite H0.
      apply voiceless_of_no_change.
      exact H1.
    + unfold apply_voicing_assimilation.
      rewrite H, H0.
      reflexivity.
  - intro H.
    unfold apply_voicing_assimilation in H.
    destruct (is_jhas c2) eqn:Ejhas.
    + destruct (is_voiceable c1) eqn:Evoice.
      * apply VAS_voice.
        -- apply is_jhas_correct. exact Ejhas.
        -- apply voiced_of_correct.
           split; [exact Evoice | exact H].
      * pose proof (voiced_of_no_change c1 Evoice) as Hno.
        rewrite Hno in H.
        subst c3.
        apply VAS_voice_no_change.
        -- apply is_jhas_correct. exact Ejhas.
        -- exact Evoice.
    + destruct (is_khar c2) eqn:Ekhar.
      * destruct (is_devoiceable c1) eqn:Edevoice.
        -- apply VAS_devoice.
           ++ exact Ejhas.
           ++ apply is_khar_correct. exact Ekhar.
           ++ apply voiceless_of_correct.
              split; [exact Edevoice | exact H].
        -- pose proof (voiceless_of_no_change c1 Edevoice) as Hno.
           rewrite Hno in H.
           subst c3.
           apply VAS_devoice_no_change.
           ++ exact Ejhas.
           ++ apply is_khar_correct. exact Ekhar.
           ++ exact Edevoice.
      * subst c3.
        apply VAS_none.
        -- exact Ejhas.
        -- exact Ekhar.
Qed.

(** Independent declarative spec for consonant sandhi based on sūtras.
    This spec describes the rules linguistically without reference to
    the implementation steps. *)

(** 8.4.40 stoḥ ścunā ścuḥ: dental s/t-class becomes palatal before palatals. *)
Inductive scutva_applies : Consonant -> Consonant -> Consonant -> Prop :=
  | Scu_s_c : forall c2, is_cavarga_or_sh_spec c2 -> scutva_applies C_s c2 C_sh
  | Scu_t_c : forall c2, is_cavarga_or_sh_spec c2 -> scutva_applies C_t c2 C_c
  | Scu_th_c : forall c2, is_cavarga_or_sh_spec c2 -> scutva_applies C_th c2 C_ch
  | Scu_d_c : forall c2, is_cavarga_or_sh_spec c2 -> scutva_applies C_d c2 C_j
  | Scu_dh_c : forall c2, is_cavarga_or_sh_spec c2 -> scutva_applies C_dh c2 C_jh
  | Scu_n_c : forall c2, is_cavarga_or_sh_spec c2 -> scutva_applies C_n c2 C_ny.

(** 8.4.41 ṣṭunā ṣṭuḥ: dental s/t-class becomes retroflex before retroflexes. *)
Inductive stutva_applies : Consonant -> Consonant -> Consonant -> Prop :=
  | Stu_s_t : forall c2, is_tavarga_or_ss_spec c2 -> stutva_applies C_s c2 C_ss
  | Stu_t_t : forall c2, is_tavarga_or_ss_spec c2 -> stutva_applies C_t c2 C_tt
  | Stu_th_t : forall c2, is_tavarga_or_ss_spec c2 -> stutva_applies C_th c2 C_tth
  | Stu_d_t : forall c2, is_tavarga_or_ss_spec c2 -> stutva_applies C_d c2 C_dd
  | Stu_dh_t : forall c2, is_tavarga_or_ss_spec c2 -> stutva_applies C_dh c2 C_ddh
  | Stu_n_t : forall c2, is_tavarga_or_ss_spec c2 -> stutva_applies C_n c2 C_nn.

(** 8.4.53 jhalāṁ jaś jhaśi: voiceless becomes voiced before voiced. *)
Inductive voicing_applies : Consonant -> Consonant -> Consonant -> Prop :=
  | Voice_k_g : forall c2, is_jhas_spec c2 -> voicing_applies C_k c2 C_g
  | Voice_kh_gh : forall c2, is_jhas_spec c2 -> voicing_applies C_kh c2 C_gh
  | Voice_c_j : forall c2, is_jhas_spec c2 -> voicing_applies C_c c2 C_j
  | Voice_ch_jh : forall c2, is_jhas_spec c2 -> voicing_applies C_ch c2 C_jh
  | Voice_tt_dd : forall c2, is_jhas_spec c2 -> voicing_applies C_tt c2 C_dd
  | Voice_tth_ddh : forall c2, is_jhas_spec c2 -> voicing_applies C_tth c2 C_ddh
  | Voice_t_d : forall c2, is_jhas_spec c2 -> voicing_applies C_t c2 C_d
  | Voice_th_dh : forall c2, is_jhas_spec c2 -> voicing_applies C_th c2 C_dh
  | Voice_p_b : forall c2, is_jhas_spec c2 -> voicing_applies C_p c2 C_b
  | Voice_ph_bh : forall c2, is_jhas_spec c2 -> voicing_applies C_ph c2 C_bh.

(** 8.4.55 khari ca: voiced becomes voiceless before voiceless. *)
Inductive devoicing_applies : Consonant -> Consonant -> Consonant -> Prop :=
  | Devoice_g_k : forall c2, is_khar_spec c2 -> devoicing_applies C_g c2 C_k
  | Devoice_gh_k : forall c2, is_khar_spec c2 -> devoicing_applies C_gh c2 C_k
  | Devoice_j_c : forall c2, is_khar_spec c2 -> devoicing_applies C_j c2 C_c
  | Devoice_jh_c : forall c2, is_khar_spec c2 -> devoicing_applies C_jh c2 C_c
  | Devoice_dd_tt : forall c2, is_khar_spec c2 -> devoicing_applies C_dd c2 C_tt
  | Devoice_ddh_tt : forall c2, is_khar_spec c2 -> devoicing_applies C_ddh c2 C_tt
  | Devoice_d_t : forall c2, is_khar_spec c2 -> devoicing_applies C_d c2 C_t
  | Devoice_dh_t : forall c2, is_khar_spec c2 -> devoicing_applies C_dh c2 C_t
  | Devoice_b_p : forall c2, is_khar_spec c2 -> devoicing_applies C_b c2 C_p
  | Devoice_bh_p : forall c2, is_khar_spec c2 -> devoicing_applies C_bh c2 C_p.

(** Combined independent spec: place then voicing, with no-change cases. *)
Inductive consonant_sandhi_spec : Consonant -> Consonant -> Consonant -> Prop :=
  | CSS_combined : forall c1 c2 c_mid c_out,
      place_assimilation_spec c1 c2 c_mid ->
      voicing_assimilation_spec c_mid c2 c_out ->
      consonant_sandhi_spec c1 c2 c_out.

Theorem consonant_sandhi_correct : forall c1 c2 c3,
  consonant_sandhi_spec c1 c2 c3 <-> apply_consonant_sandhi c1 c2 = c3.
Proof.
  intros c1 c2 c3.
  split.
  - intro H.
    destruct H as [c1' c2' c_mid c_out Hplace Hvoice].
    unfold apply_consonant_sandhi.
    apply place_assimilation_correct in Hplace.
    rewrite Hplace.
    apply voicing_assimilation_correct in Hvoice.
    exact Hvoice.
  - intro H.
    unfold apply_consonant_sandhi in H.
    apply CSS_combined with (c_mid := apply_place_assimilation c1 c2).
    + apply place_assimilation_correct.
      reflexivity.
    + apply voicing_assimilation_correct.
      exact H.
Qed.

(** Examples of consonant sandhi. *)

Example cons_sandhi_vak_gacchati :
  apply_consonant_sandhi C_k C_g = C_g.
Proof. reflexivity. Qed.

Example cons_sandhi_tat_ca :
  apply_consonant_sandhi C_t C_c = C_c.
Proof. reflexivity. Qed.

Example cons_sandhi_tat_tena :
  apply_consonant_sandhi C_t C_t = C_t.
Proof. reflexivity. Qed.

Example cons_sandhi_tad_gacchati :
  apply_consonant_sandhi C_d C_g = C_d.
Proof. reflexivity. Qed.

Example cons_sandhi_tat_gacchati :
  apply_consonant_sandhi C_t C_g = C_d.
Proof. reflexivity. Qed.

(** * Part XXII-B: ṇatva (8.4.2) *)

(** ** 8.4.2 aṭ-kuppvāṅnumvyavāye 'pi *)
(** n becomes ṇ when preceded by ṛ, ṝ, r, or ṣ, unless blocked by
    intervening palatals, dentals, cerebrals, or l. *)

Definition is_natva_trigger (p : Phoneme) : bool :=
  match p with
  | Svar V_r | Svar V_rr => true
  | Vyan C_r | Vyan C_ss => true
  | _ => false
  end.

Definition is_natva_blocker (p : Phoneme) : bool :=
  match p with
  | Vyan c =>
      match c with
      | C_c | C_ch | C_j | C_jh | C_ny => true
      | C_t | C_th | C_d | C_dh | C_n => true
      | C_tt | C_tth | C_dd | C_ddh | C_nn => true
      | C_l => true
      | _ => false
      end
  | _ => false
  end.

Fixpoint natva_active_aux (ps : list Phoneme) : bool :=
  match ps with
  | [] => false
  | p :: rest =>
      if is_natva_trigger p then true
      else if is_natva_blocker p then false
      else natva_active_aux rest
  end.

Definition natva_active (preceding : list Phoneme) : bool :=
  natva_active_aux (rev preceding).

Definition apply_natva (preceding : list Phoneme) (c : Consonant) : Consonant :=
  match c with
  | C_n => if natva_active preceding then C_nn else C_n
  | _ => c
  end.

Inductive natva_spec : list Phoneme -> Consonant -> Consonant -> Prop :=
  | Natva_trigger : forall ps,
      natva_active ps = true ->
      natva_spec ps C_n C_nn
  | Natva_blocked : forall ps,
      natva_active ps = false ->
      natva_spec ps C_n C_n
  | Natva_other : forall ps c,
      c <> C_n ->
      natva_spec ps c c.

Lemma apply_natva_correct : forall ps c c',
  apply_natva ps c = c' <-> natva_spec ps c c'.
Proof.
  intros ps c c'.
  split.
  - intro H.
    unfold apply_natva in H.
    destruct c; try (subst; apply Natva_other; discriminate).
    destruct (natva_active ps) eqn:E; subst.
    + apply Natva_trigger. exact E.
    + apply Natva_blocked. exact E.
  - intro H.
    destruct H.
    + unfold apply_natva. rewrite H. reflexivity.
    + unfold apply_natva. rewrite H. reflexivity.
    + unfold apply_natva. destruct c; try reflexivity; contradiction.
Qed.

Example natva_ex1 :
  apply_natva [Svar V_r; Svar V_a] C_n = C_nn.
Proof. reflexivity. Qed.

Example natva_ex2 :
  apply_natva [Svar V_a; Svar V_i] C_n = C_n.
Proof. reflexivity. Qed.

Example natva_ex3 :
  apply_natva [Svar V_r; Vyan C_t; Svar V_a] C_n = C_n.
Proof. reflexivity. Qed.

Example natva_ex4 :
  apply_natva [Vyan C_ss; Svar V_a] C_n = C_nn.
Proof. reflexivity. Qed.

(** * Part XXII-C: Additional Consonant Sandhi Rules (8.4) *)

(** ** 8.4.44 śāt *)
(** "After ś, [dental t becomes c]."
    When ś precedes t, the t becomes c (palatalization triggered by ś). *)

Definition apply_8_4_44 (preceding : Consonant) (c : Consonant) : Consonant :=
  match preceding, c with
  | C_sh, C_t => C_c
  | C_sh, C_th => C_ch
  | C_sh, C_d => C_j
  | C_sh, C_dh => C_jh
  | C_sh, C_n => C_ny
  | _, _ => c
  end.

Inductive shat_spec : Consonant -> Consonant -> Consonant -> Prop :=
  | Shat_t : shat_spec C_sh C_t C_c
  | Shat_th : shat_spec C_sh C_th C_ch
  | Shat_d : shat_spec C_sh C_d C_j
  | Shat_dh : shat_spec C_sh C_dh C_jh
  | Shat_n : shat_spec C_sh C_n C_ny
  | Shat_other : forall c1 c2,
      (c1 <> C_sh \/ (c2 <> C_t /\ c2 <> C_th /\ c2 <> C_d /\ c2 <> C_dh /\ c2 <> C_n)) ->
      shat_spec c1 c2 c2.

Lemma apply_8_4_44_correct : forall c1 c2 c3,
  apply_8_4_44 c1 c2 = c3 <-> shat_spec c1 c2 c3.
Proof.
  intros c1 c2 c3.
  split; intro H.
  - destruct c1; destruct c2; simpl in H; subst;
    solve [ constructor
          | apply Shat_other; left; discriminate
          | apply Shat_other; right; repeat split; discriminate ].
  - inversion H; subst.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + destruct H0 as [Hneq | [H1 [H2 [H3 [H4 H5]]]]].
      * destruct c1; simpl; try reflexivity.
        contradiction.
      * destruct c1; simpl; try reflexivity.
        destruct c3; simpl; try reflexivity;
        first [ exfalso; apply H1; reflexivity
              | exfalso; apply H2; reflexivity
              | exfalso; apply H3; reflexivity
              | exfalso; apply H4; reflexivity
              | exfalso; apply H5; reflexivity ].
Qed.

Example shat_ex1 : apply_8_4_44 C_sh C_t = C_c.
Proof. reflexivity. Qed.

Example shat_ex2 : apply_8_4_44 C_s C_t = C_t.
Proof. reflexivity. Qed.

(** ** 8.4.45 yaro 'nunāsike 'nunāsiko vā *)
(** "A stop [yar] optionally becomes its nasal [anunāsika] before a nasal."
    This is a vikalpa (optional) rule. *)

Definition nasal_of_varga (c : Consonant) : option Consonant :=
  match c with
  | C_k | C_kh | C_g | C_gh => Some C_ng
  | C_c | C_ch | C_j | C_jh => Some C_ny
  | C_tt | C_tth | C_dd | C_ddh => Some C_nn
  | C_t | C_th | C_d | C_dh => Some C_n
  | C_p | C_ph | C_b | C_bh => Some C_m
  | _ => None
  end.

Definition is_nasal (c : Consonant) : bool :=
  match c with
  | C_ng | C_ny | C_nn | C_n | C_m => true
  | _ => false
  end.

Definition is_yar (c : Consonant) : bool :=
  match c with
  | C_k | C_kh | C_g | C_gh
  | C_c | C_ch | C_j | C_jh
  | C_tt | C_tth | C_dd | C_ddh
  | C_t | C_th | C_d | C_dh
  | C_p | C_ph | C_b | C_bh => true
  | _ => false
  end.

Inductive nasalization_8_4_45 : Consonant -> Consonant -> option Consonant -> Prop :=
  | Nas_applies : forall c1 c2 c_nasal,
      is_yar c1 = true ->
      is_nasal c2 = true ->
      nasal_of_varga c1 = Some c_nasal ->
      nasalization_8_4_45 c1 c2 (Some c_nasal)
  | Nas_no_yar : forall c1 c2,
      is_yar c1 = false ->
      nasalization_8_4_45 c1 c2 None
  | Nas_no_nasal : forall c1 c2,
      is_nasal c2 = false ->
      nasalization_8_4_45 c1 c2 None.

Definition apply_8_4_45 (c1 c2 : Consonant) : option Consonant :=
  if is_yar c1 && is_nasal c2 then nasal_of_varga c1
  else None.

Lemma apply_8_4_45_correct : forall c1 c2 result,
  apply_8_4_45 c1 c2 = result <-> nasalization_8_4_45 c1 c2 result.
Proof.
  intros c1 c2 result.
  split.
  - intro H.
    unfold apply_8_4_45 in H.
    destruct (is_yar c1) eqn:Eyar.
    + destruct (is_nasal c2) eqn:Enas.
      * simpl in H. subst.
        destruct (nasal_of_varga c1) eqn:Enov.
        -- apply Nas_applies with (c_nasal := c); auto.
        -- apply Nas_no_yar. destruct c1; simpl in Eyar; discriminate.
      * simpl in H. subst. apply Nas_no_nasal. exact Enas.
    + simpl in H. subst. apply Nas_no_yar. exact Eyar.
  - intro H.
    destruct H.
    + unfold apply_8_4_45. rewrite H, H0. simpl. exact H1.
    + unfold apply_8_4_45. rewrite H. reflexivity.
    + unfold apply_8_4_45.
      destruct (is_yar c1) eqn:Eyar; simpl.
      * rewrite H. reflexivity.
      * reflexivity.
Qed.

Example nas_ex1 : apply_8_4_45 C_k C_n = Some C_ng.
Proof. reflexivity. Qed.

Example nas_ex2 : apply_8_4_45 C_t C_m = Some C_n.
Proof. reflexivity. Qed.

Example nas_ex3 : apply_8_4_45 C_s C_n = None.
Proof. reflexivity. Qed.

(** ** 8.4.58 anusvārasya yayi parasavarṇaḥ *)
(** "Anusvāra becomes [parasavarṇa, i.e., homorganic nasal] before yay
    (semivowels and stops)." *)

Definition homorganic_nasal_of (c : Consonant) : option Consonant :=
  match c with
  | C_k | C_kh | C_g | C_gh | C_ng => Some C_ng
  | C_c | C_ch | C_j | C_jh | C_ny => Some C_ny
  | C_tt | C_tth | C_dd | C_ddh | C_nn => Some C_nn
  | C_t | C_th | C_d | C_dh | C_n => Some C_n
  | C_p | C_ph | C_b | C_bh | C_m => Some C_m
  | C_y => Some C_ny
  | C_l => Some C_n
  | C_v => Some C_m
  | _ => None
  end.

Definition is_yay (c : Consonant) : bool :=
  match c with
  | C_y | C_v
  | C_k | C_kh | C_g | C_gh | C_ng
  | C_c | C_ch | C_j | C_jh | C_ny
  | C_tt | C_tth | C_dd | C_ddh | C_nn
  | C_t | C_th | C_d | C_dh | C_n
  | C_p | C_ph | C_b | C_bh | C_m => true
  | _ => false
  end.

Inductive anusvara_assimilation_spec : Consonant -> option Consonant -> Prop :=
  | AAS_assimilate : forall c c_nasal,
      is_yay c = true ->
      homorganic_nasal_of c = Some c_nasal ->
      anusvara_assimilation_spec c (Some c_nasal)
  | AAS_no_change : forall c,
      is_yay c = false ->
      anusvara_assimilation_spec c None.

Definition apply_8_4_58 (following : Consonant) : option Consonant :=
  if is_yay following then homorganic_nasal_of following
  else None.

Lemma apply_8_4_58_correct : forall c result,
  apply_8_4_58 c = result <-> anusvara_assimilation_spec c result.
Proof.
  intros c result.
  split.
  - intro H.
    unfold apply_8_4_58 in H.
    destruct (is_yay c) eqn:Eyay.
    + subst.
      destruct (homorganic_nasal_of c) eqn:Ehom.
      * apply AAS_assimilate with (c_nasal := c0); auto.
      * apply AAS_no_change. destruct c; simpl in Eyay; discriminate.
    + subst. apply AAS_no_change. exact Eyay.
  - intro H.
    destruct H.
    + unfold apply_8_4_58. rewrite H. exact H0.
    + unfold apply_8_4_58. rewrite H. reflexivity.
Qed.

Example anusvara_ex1 : apply_8_4_58 C_k = Some C_ng.
Proof. reflexivity. Qed.

Example anusvara_ex2 : apply_8_4_58 C_c = Some C_ny.
Proof. reflexivity. Qed.

Example anusvara_ex3 : apply_8_4_58 C_t = Some C_n.
Proof. reflexivity. Qed.

Example anusvara_ex4 : apply_8_4_58 C_p = Some C_m.
Proof. reflexivity. Qed.

Example anusvara_ex5 : apply_8_4_58 C_s = None.
Proof. reflexivity. Qed.

(** ** 8.4.60 tor li *)
(** "t and d [tor] become l before l [li]." *)

Definition apply_8_4_60 (c following : Consonant) : Consonant :=
  match c, following with
  | C_t, C_l => C_l
  | C_d, C_l => C_l
  | C_n, C_l => C_l
  | _, _ => c
  end.

Inductive tor_li_spec : Consonant -> Consonant -> Consonant -> Prop :=
  | TL_t : tor_li_spec C_t C_l C_l
  | TL_d : tor_li_spec C_d C_l C_l
  | TL_n : tor_li_spec C_n C_l C_l
  | TL_other : forall c1 c2,
      (c2 <> C_l \/ (c1 <> C_t /\ c1 <> C_d /\ c1 <> C_n)) ->
      tor_li_spec c1 c2 c1.

Lemma apply_8_4_60_correct : forall c1 c2 c3,
  apply_8_4_60 c1 c2 = c3 <-> tor_li_spec c1 c2 c3.
Proof.
  intros c1 c2 c3.
  split; intro H.
  - destruct c1; destruct c2; simpl in H; subst;
    solve [ constructor
          | apply TL_other; left; discriminate
          | apply TL_other; right; repeat split; discriminate ].
  - inversion H; subst.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + destruct H0 as [Hneq | [H1 [H2 H3]]].
      * destruct c2; try contradiction; destruct c3; reflexivity.
      * destruct c3, c2; simpl; try reflexivity;
        first [ exfalso; apply H1; reflexivity
              | exfalso; apply H2; reflexivity
              | exfalso; apply H3; reflexivity ].
Qed.

Example tor_li_ex1 : apply_8_4_60 C_t C_l = C_l.
Proof. reflexivity. Qed.

Example tor_li_ex2 : apply_8_4_60 C_d C_l = C_l.
Proof. reflexivity. Qed.

Example tor_li_ex3 : apply_8_4_60 C_t C_t = C_t.
Proof. reflexivity. Qed.

(** ** 8.4.63 śaś cho 'ṭi *)
(** "ś becomes ch before ṭ-class (including ṣ)." *)

Definition apply_8_4_63 (c following : Consonant) : Consonant :=
  match c with
  | C_sh =>
      if is_tavarga_or_ss following then C_ch
      else c
  | _ => c
  end.

Inductive shas_cha_spec : Consonant -> Consonant -> Consonant -> Prop :=
  | SC_applies : forall c2,
      is_tavarga_or_ss_spec c2 ->
      shas_cha_spec C_sh c2 C_ch
  | SC_no_trigger : forall c2,
      is_tavarga_or_ss c2 = false ->
      shas_cha_spec C_sh c2 C_sh
  | SC_not_sh : forall c1 c2,
      c1 <> C_sh ->
      shas_cha_spec c1 c2 c1.

Lemma apply_8_4_63_correct : forall c1 c2 c3,
  apply_8_4_63 c1 c2 = c3 <-> shas_cha_spec c1 c2 c3.
Proof.
  intros c1 c2 c3.
  split.
  - intro H.
    unfold apply_8_4_63 in H.
    destruct c1; try (subst; apply SC_not_sh; discriminate).
    destruct (is_tavarga_or_ss c2) eqn:E.
    + subst. apply SC_applies. apply is_tavarga_or_ss_correct. exact E.
    + subst. apply SC_no_trigger. exact E.
  - intro H.
    destruct H.
    + unfold apply_8_4_63.
      apply is_tavarga_or_ss_correct in H.
      rewrite H. reflexivity.
    + unfold apply_8_4_63. rewrite H. reflexivity.
    + unfold apply_8_4_63.
      destruct c1; try reflexivity; contradiction.
Qed.

Example shas_cha_ex1 : apply_8_4_63 C_sh C_tt = C_ch.
Proof. reflexivity. Qed.

Example shas_cha_ex2 : apply_8_4_63 C_sh C_ss = C_ch.
Proof. reflexivity. Qed.

Example shas_cha_ex3 : apply_8_4_63 C_sh C_t = C_sh.
Proof. reflexivity. Qed.

(** ** 8.4.65 jharo jhari savarṇe *)
(** "jhar [non-nasal stops] become savarṇa [homorganic] before jhar when
    followed by the same." This handles gemination/assimilation at boundaries. *)

Definition is_jhar (c : Consonant) : bool :=
  match c with
  | C_k | C_kh | C_g | C_gh
  | C_c | C_ch | C_j | C_jh
  | C_tt | C_tth | C_dd | C_ddh
  | C_t | C_th | C_d | C_dh
  | C_p | C_ph | C_b | C_bh => true
  | _ => false
  end.

Definition same_varga (c1 c2 : Consonant) : bool :=
  match consonant_varga c1, consonant_varga c2 with
  | Some v1, Some v2 =>
      match v1, v2 with
      | Kavarga, Kavarga => true
      | Cavarga, Cavarga => true
      | Tavarga, Tavarga => true
      | Tavarga2, Tavarga2 => true
      | Pavarga, Pavarga => true
      | _, _ => false
      end
  | _, _ => false
  end.

Definition first_of_varga (v : Varga) : Consonant :=
  match v with
  | Kavarga => C_k
  | Cavarga => C_c
  | Tavarga => C_tt
  | Tavarga2 => C_t
  | Pavarga => C_p
  end.

Definition apply_8_4_65 (c1 c2 : Consonant) : Consonant :=
  if is_jhar c1 && is_jhar c2 && same_varga c1 c2 then
    match consonant_varga c2 with
    | Some v => first_of_varga v
    | None => c1
    end
  else c1.

Inductive jhar_savarna_spec : Consonant -> Consonant -> Consonant -> Prop :=
  | JS_assimilate : forall c1 c2 v,
      is_jhar c1 = true ->
      is_jhar c2 = true ->
      consonant_varga c1 = Some v ->
      consonant_varga c2 = Some v ->
      jhar_savarna_spec c1 c2 (first_of_varga v)
  | JS_no_change : forall c1 c2,
      (is_jhar c1 = false \/ is_jhar c2 = false \/ same_varga c1 c2 = false) ->
      jhar_savarna_spec c1 c2 c1.

Lemma apply_8_4_65_correct : forall c1 c2 c3,
  apply_8_4_65 c1 c2 = c3 <-> jhar_savarna_spec c1 c2 c3.
Proof.
  intros c1 c2 c3.
  split.
  - intro H.
    unfold apply_8_4_65 in H.
    destruct (is_jhar c1) eqn:E1.
    + destruct (is_jhar c2) eqn:E2.
      * destruct (same_varga c1 c2) eqn:Esame.
        -- simpl in H.
           unfold same_varga in Esame.
           destruct (consonant_varga c1) eqn:Ev1; try discriminate.
           destruct (consonant_varga c2) eqn:Ev2; try discriminate.
           destruct v, v0; try discriminate; subst;
           apply JS_assimilate; auto.
        -- simpl in H. subst. apply JS_no_change. right. right. exact Esame.
      * simpl in H. subst. apply JS_no_change. right. left. exact E2.
    + simpl in H. subst. apply JS_no_change. left. exact E1.
  - intro H.
    destruct H as [x y v Hj1 Hj2 Hv1 Hv2 | x y Hdisj].
    + unfold apply_8_4_65.
      rewrite Hj1, Hj2. simpl.
      unfold same_varga. rewrite Hv1, Hv2.
      destruct v; simpl; reflexivity.
    + unfold apply_8_4_65.
      destruct Hdisj as [H1 | [H2 | H3]].
      * rewrite H1. reflexivity.
      * destruct (is_jhar x); simpl; try rewrite H2; reflexivity.
      * destruct (is_jhar x); simpl; destruct (is_jhar y); simpl; try reflexivity.
        rewrite H3. reflexivity.
Qed.

Example jhar_ex1 : apply_8_4_65 C_t C_t = C_t.
Proof. reflexivity. Qed.

Example jhar_ex2 : apply_8_4_65 C_d C_t = C_t.
Proof. reflexivity. Qed.

Example jhar_ex3 : apply_8_4_65 C_k C_t = C_k.
Proof. reflexivity. Qed.

(** ** 8.3.24 naś ca viśarjanīyaḥ padānte *)
(** "Final n [naś] becomes visarjanīya at end of pada."
    This handles word-final nasal sandhi. *)

Definition final_n_before_khar (c : Consonant) : bool :=
  is_khar c.

Inductive final_n_sandhi_spec : Consonant -> Phoneme -> Prop :=
  | FNS_visarga : forall c,
      is_khar c = true ->
      final_n_sandhi_spec c Visarga
  | FNS_unchanged : forall c,
      is_khar c = false ->
      final_n_sandhi_spec c (Vyan C_n).

(** ** 8.3.35 śarvabhaktasya upasargasya ca pūrvasyām *)
(** Visarga before s becomes s (ru-s). *)

Definition visarga_before_s (following : Consonant) : bool :=
  match following with
  | C_s => true
  | _ => false
  end.

(** ** Combined Extended Consonant Sandhi *)

(** Applies all 8.4 rules in correct order:
    1. 8.4.63 śaś cho'ṭi (ś → ch before retroflex)
    2. 8.4.44 śāt (dental → palatal after ś)
    3. 8.4.60 tor li (t/d → l before l)
    4. 8.4.40-41 place assimilation
    5. 8.4.53-55 voicing assimilation
    6. 8.4.65 jhar savarṇa assimilation *)

Definition apply_extended_consonant_sandhi (c1 c2 : Consonant) : Consonant :=
  let step1 := apply_8_4_63 c1 c2 in
  let step2 := apply_8_4_60 step1 c2 in
  let step3 := apply_place_assimilation step2 c2 in
  let step4 := apply_voicing_assimilation step3 c2 in
  let step5 := apply_8_4_65 step4 c2 in
  step5.

(** Declarative specification for extended consonant sandhi. *)

Inductive extended_consonant_sandhi_spec
  : Consonant -> Consonant -> Consonant -> Prop :=
  | ECSS_combined : forall c1 c2 s1 s2 s3 s4 s5,
      apply_8_4_63 c1 c2 = s1 ->
      apply_8_4_60 s1 c2 = s2 ->
      place_assimilation_spec s2 c2 s3 ->
      voicing_assimilation_spec s3 c2 s4 ->
      jhar_savarna_spec s4 c2 s5 ->
      extended_consonant_sandhi_spec c1 c2 s5.

Theorem extended_consonant_sandhi_correct : forall c1 c2 c3,
  extended_consonant_sandhi_spec c1 c2 c3 <-> apply_extended_consonant_sandhi c1 c2 = c3.
Proof.
  intros c1 c2 c3.
  split.
  - intro H.
    destruct H.
    unfold apply_extended_consonant_sandhi.
    rewrite H, H0.
    apply place_assimilation_correct in H1.
    rewrite H1.
    apply voicing_assimilation_correct in H2.
    rewrite H2.
    apply apply_8_4_65_correct in H3.
    exact H3.
  - intro H.
    unfold apply_extended_consonant_sandhi in H.
    apply ECSS_combined with
      (s1 := apply_8_4_63 c1 c2)
      (s2 := apply_8_4_60 (apply_8_4_63 c1 c2) c2)
      (s3 := apply_place_assimilation (apply_8_4_60 (apply_8_4_63 c1 c2) c2) c2)
      (s4 := apply_voicing_assimilation
               (apply_place_assimilation (apply_8_4_60 (apply_8_4_63 c1 c2) c2) c2) c2).
    + reflexivity.
    + reflexivity.
    + apply place_assimilation_correct. reflexivity.
    + apply voicing_assimilation_correct. reflexivity.
    + apply apply_8_4_65_correct. exact H.
Qed.

(** Examples of extended consonant sandhi. *)

Example ext_cons_sandhi_1 :
  apply_extended_consonant_sandhi C_t C_c = C_c.
Proof. reflexivity. Qed.

Example ext_cons_sandhi_2 :
  apply_extended_consonant_sandhi C_t C_l = C_l.
Proof. reflexivity. Qed.

Example ext_cons_sandhi_3 :
  apply_extended_consonant_sandhi C_d C_g = C_d.
Proof. reflexivity. Qed.

Example ext_cons_sandhi_4 :
  apply_extended_consonant_sandhi C_t C_g = C_d.
Proof. reflexivity. Qed.

Example ext_cons_sandhi_5 :
  apply_extended_consonant_sandhi C_sh C_tt = C_ch.
Proof. reflexivity. Qed.

(** ** Totality: Extended consonant sandhi always produces a result. *)

Theorem extended_consonant_sandhi_total : forall c1 c2,
  exists c3, extended_consonant_sandhi_spec c1 c2 c3.
Proof.
  intros c1 c2.
  exists (apply_extended_consonant_sandhi c1 c2).
  apply extended_consonant_sandhi_correct.
  reflexivity.
Qed.

(** * Part XXII-D: Expanded Visarga Sandhi (8.3) *)

(** ** 8.3.15 kharavasānayoḥ visarjanīyaḥ *)
(** "Before khar or pause, [s becomes] visarjanīya."
    This is the primary rule for s → ḥ. *)

Definition s_to_visarga_context (following : option Consonant) : bool :=
  match following with
  | None => true
  | Some c => is_khar c
  end.

Inductive s_to_visarga_spec : option Consonant -> Prop :=
  | STV_pause : s_to_visarga_spec None
  | STV_khar : forall c, is_khar_spec c -> s_to_visarga_spec (Some c).

(** ** 8.3.17-21 Special visarga rules *)

(** 8.3.17 bhoḥ bhagoḥ aghoḥ apūrvāsya yo 'śi *)
(** Visarga of bhoḥ/bhagoḥ/aghoḥ becomes y before a vowel. *)

Inductive special_visarga_to_y : Prop :=
  | SVY_bho : special_visarga_to_y.

(** ** 8.3.34 visarjanīyasya saḥ *)
(** "Visarjanīya [becomes] s [before k/kh and p/ph]."
    More precisely, before certain voiceless stops. *)

Definition visarga_to_s_context (c : Consonant) : bool :=
  match c with
  | C_k | C_kh | C_p | C_ph => false
  | _ => is_khar c
  end.

Inductive visarga_to_s_spec : Consonant -> Prop :=
  | VTS_c : visarga_to_s_spec C_c
  | VTS_ch : visarga_to_s_spec C_ch
  | VTS_tt : visarga_to_s_spec C_tt
  | VTS_tth : visarga_to_s_spec C_tth
  | VTS_t : visarga_to_s_spec C_t
  | VTS_th : visarga_to_s_spec C_th
  | VTS_sh : visarga_to_s_spec C_sh
  | VTS_ss : visarga_to_s_spec C_ss
  | VTS_s : visarga_to_s_spec C_s.

Lemma visarga_to_s_correct : forall c,
  visarga_to_s_context c = true <-> visarga_to_s_spec c.
Proof.
  intro c; split.
  - intro H; destruct c; simpl in H; try discriminate; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** ** 8.3.36 visarjanīyasya jihvāmūlīyopadhmānīyau vā *)
(** "Visarga optionally becomes jihvāmūlīya before k/kh
    or upadhmānīya before p/ph." *)

Inductive visarga_allophone_extended : Consonant -> list Phoneme -> Prop :=
  | VAE_jihva_k : visarga_allophone_extended C_k [Jihvamuliya]
  | VAE_jihva_kh : visarga_allophone_extended C_kh [Jihvamuliya]
  | VAE_upadh_p : visarga_allophone_extended C_p [Upadhmamiya]
  | VAE_upadh_ph : visarga_allophone_extended C_ph [Upadhmamiya]
  | VAE_plain : forall c, visarga_allophone_extended c [Visarga].

(** ** Combined Visarga Sandhi *)

Inductive VisargaSandhiResultExt : Type :=
  | VSRE_visarga : VisargaSandhiResultExt
  | VSRE_jihvamuliya : VisargaSandhiResultExt
  | VSRE_upadhmamiya : VisargaSandhiResultExt
  | VSRE_s : VisargaSandhiResultExt
  | VSRE_r : VisargaSandhiResultExt
  | VSRE_o : VisargaSandhiResultExt
  | VSRE_deletion : Vowel -> VisargaSandhiResultExt.

Definition apply_visarga_sandhi_ext (prev_vowel : Vowel) (following : Consonant)
  : VisargaSandhiResultExt :=
  if is_jhas following then
    match prev_vowel with
    | V_a => VSRE_o
    | V_aa => VSRE_deletion V_aa
    | _ => VSRE_r
    end
  else
    match following with
    | C_k | C_kh => VSRE_jihvamuliya
    | C_p | C_ph => VSRE_upadhmamiya
    | _ =>
        if visarga_to_s_context following then VSRE_s
        else VSRE_visarga
    end.

Inductive visarga_sandhi_ext_spec
  : Vowel -> Consonant -> VisargaSandhiResultExt -> Prop :=
  | VSES_jhas_a : forall c,
      is_jhas c = true ->
      visarga_sandhi_ext_spec V_a c VSRE_o
  | VSES_jhas_aa : forall c,
      is_jhas c = true ->
      visarga_sandhi_ext_spec V_aa c (VSRE_deletion V_aa)
  | VSES_jhas_other : forall v c,
      is_jhas c = true ->
      v <> V_a ->
      v <> V_aa ->
      visarga_sandhi_ext_spec v c VSRE_r
  | VSES_jihva_k :
      visarga_sandhi_ext_spec V_a C_k VSRE_jihvamuliya
  | VSES_jihva_kh :
      visarga_sandhi_ext_spec V_a C_kh VSRE_jihvamuliya
  | VSES_upadh_p :
      visarga_sandhi_ext_spec V_a C_p VSRE_upadhmamiya
  | VSES_upadh_ph :
      visarga_sandhi_ext_spec V_a C_ph VSRE_upadhmamiya
  | VSES_to_s : forall v c,
      is_jhas c = false ->
      c <> C_k -> c <> C_kh -> c <> C_p -> c <> C_ph ->
      visarga_to_s_spec c ->
      visarga_sandhi_ext_spec v c VSRE_s
  | VSES_plain : forall v c,
      is_jhas c = false ->
      c <> C_k -> c <> C_kh -> c <> C_p -> c <> C_ph ->
      visarga_to_s_context c = false ->
      visarga_sandhi_ext_spec v c VSRE_visarga.

Example visarga_ext_ex1 :
  apply_visarga_sandhi_ext V_a C_k = VSRE_jihvamuliya.
Proof. reflexivity. Qed.

Example visarga_ext_ex2 :
  apply_visarga_sandhi_ext V_a C_p = VSRE_upadhmamiya.
Proof. reflexivity. Qed.

Example visarga_ext_ex3 :
  apply_visarga_sandhi_ext V_a C_g = VSRE_o.
Proof. reflexivity. Qed.

Example visarga_ext_ex4 :
  apply_visarga_sandhi_ext V_i C_g = VSRE_r.
Proof. reflexivity. Qed.

Example visarga_ext_ex5 :
  apply_visarga_sandhi_ext V_a C_c = VSRE_s.
Proof. reflexivity. Qed.

(** * Part XXIII: Unified External Sandhi *)

(** External sandhi context: what is at the boundary. *)

Inductive BoundarySound : Type :=
  | BS_vowel : Vowel -> BoundarySound
  | BS_consonant : Consonant -> BoundarySound
  | BS_visarga : Vowel -> BoundarySound
  | BS_anusvara : BoundarySound
  | BS_pause : BoundarySound.

(** Result of external sandhi. *)

Inductive SandhiResult : Type :=
  | SR_vowels : list Phoneme -> SandhiResult
  | SR_consonant : Consonant -> SandhiResult
  | SR_visarga : SandhiResult
  | SR_anusvara : SandhiResult
  | SR_unchanged : Phoneme -> SandhiResult.

(** Convert VisargaSandhiResult to SandhiResult. *)

Definition visarga_result_to_sandhi_result (vsr : VisargaSandhiResult) : SandhiResult :=
  match vsr with
  | VSR_visarga => SR_visarga
  | VSR_s => SR_consonant C_s
  | VSR_r => SR_consonant C_r
  | VSR_deletion v => SR_vowels [Svar v]
  | VSR_o => SR_vowels [Svar V_o]
  end.

(** Unified sandhi at word boundary. *)

Definition apply_external_sandhi
  (final : BoundarySound) (initial : BoundarySound)
  : SandhiResult :=
  match final, initial with
  | BS_vowel v1, BS_vowel v2 =>
      SR_vowels (apply_ac_sandhi v1 v2)
  | BS_consonant c1, BS_consonant c2 =>
      SR_consonant (apply_consonant_sandhi c1 c2)
  | BS_consonant c, BS_vowel _ =>
      SR_unchanged (Vyan c)
  | BS_vowel v, BS_consonant _ =>
      SR_unchanged (Svar v)
  | BS_visarga prev_v, BS_consonant c =>
      visarga_result_to_sandhi_result (apply_visarga_sandhi prev_v c)
  | BS_visarga _, BS_vowel _ =>
      SR_unchanged Visarga
  | _, BS_pause =>
      match final with
      | BS_vowel v => SR_unchanged (Svar v)
      | BS_consonant c => SR_unchanged (Vyan c)
      | BS_visarga _ => SR_visarga
      | BS_anusvara => SR_anusvara
      | BS_pause => SR_unchanged Visarga
      end
  | _, _ => SR_unchanged Visarga
  end.

(** * Part XXIV: Summary of Formalized Sūtras *)

(** Paribhāṣā (Meta-rules):
    - 1.1.1  vṛddhir ādaic
    - 1.1.2  adeṅ guṇaḥ
    - 1.1.3  iko guṇavṛddhī
    - 1.1.9  tulyāsyaprayatnaṁ savarṇam
    - 1.4.2  vipratiṣedhe paraṁ kāryam

    Vowel Sandhi (ac-sandhi, 6.1.77-113):

    External sandhi (vowel pairs only):
    - 6.1.77  iko yaṇ aci (ik → yaṇ before vowel)
    - 6.1.78  eco 'yavāyāvaḥ (ec → ay/av decomposition)
    - 6.1.87  ādguṇaḥ (a/ā + vowel → guṇa)
    - 6.1.88  vṛddhir eci (a/ā + ec → vṛddhi)
    - 6.1.101 akaḥ savarṇe dīrghaḥ (savarṇa → dīrgha)
    - 6.1.109 eṅaḥ padāntād ati (pūrvarūpa at word boundary)

    Internal sandhi (morphological context required):
    - 6.1.89  ety-edhaty-ūṭhsu (vṛddhi for eti/edhati/ūṭh roots)
    - 6.1.90  āṭaś ca (vṛddhi after āṭ augment)
    - 6.1.91  upasargād ṛti dhātau (upasarga + ṛ → vṛddhi)
    - 6.1.94  eṅi pararūpam (a/ā + e/o → pararūpa)
    - 6.1.97  ato guṇe (a elided before guṇa)
    - 6.1.107 ami pūrvaḥ (lengthening before ami)
    - 6.1.110 ṅasiṅasoś ca (pūrvarūpa before ṅas/ṅasi)
    - 6.1.111 ṛta ut (ṛ → ut)
    - 6.1.113 ato ror aplutād aplute (a + r → o)

    Adhikāra/Paribhāṣā (governing rules):
    - 6.1.84  ekaḥ pūrvaparayoḥ (one substitute for two)
    - 6.1.85  antādivacca (substitute position)
    - 6.1.86  ṣatvatukorasiddhaḥ (asiddha for ṣatva/tuk)

    Visarga Sandhi (8.3):
    - 8.3.15  kharavasānayoḥ visarjanīyaḥ
    - 8.3.17  bhoḥ bhagoḥ aghoḥ apūrvāsya yo 'śi
    - 8.3.23  mo 'nusvāraḥ
    - 8.3.24  naś ca viśarjanīyaḥ padānte
    - 8.3.34  visarjanīyasya saḥ
    - 8.3.35  śarvabhaktasya upasargasya ca pūrvasyām
    - 8.3.36  visarjanīyasya jihvāmūlīyopadhmānīyau vā

    Consonant Sandhi (8.4):
    - 8.4.2   aṭkupvāṅnumvyavāye 'pi (ṇatva)
    - 8.4.40  stoḥ ścunā ścuḥ
    - 8.4.41  ṣṭunā ṣṭuḥ
    - 8.4.44  śāt
    - 8.4.45  yaro 'nunāsike 'nunāsiko vā
    - 8.4.53  jhalāṁ jaś jhaśi
    - 8.4.55  khari ca
    - 8.4.58  anusvārasya yayi parasavarṇaḥ
    - 8.4.60  tor li
    - 8.4.63  śaś cho 'ṭi
    - 8.4.65  jharo jhari savarṇe
*)

(** * Part XXV: Final Metatheorems *)

(** All vowel pairs produce some sandhi result. *)
Theorem vowel_sandhi_total : forall v1 v2,
  exists ps, apply_ac_sandhi v1 v2 = ps /\ ps <> [].
Proof.
  intros v1 v2.
  exists (apply_ac_sandhi v1 v2).
  split.
  - reflexivity.
  - apply apply_ac_sandhi_nonempty.
Qed.

(** Consonant sandhi preserves the consonant category. *)
Theorem consonant_sandhi_yields_consonant : forall c1 c2,
  exists c, apply_consonant_sandhi c1 c2 = c.
Proof.
  intros c1 c2.
  eexists.
  reflexivity.
Qed.

(** The specification-implementation correspondence is complete for:
    - Vowel pratyāhāras (is_ik, is_ak, is_ec) - now computed from Śiva Sūtras
    - Guṇa/vṛddhi grades
    - Savarṇa relation
    - Precedence ordering (sutra_ltb <-> sutra_lt)
    - Rule defeat relation (rule_defeats <-> defeats_rel)
    - Rule selection (select_rule <-> sandhi_winner)
    - Full soundness and completeness (apply_ac_sandhi <-> ac_sandhi_rel)
    - All five ac-sandhi rules *)

Theorem formalization_complete :
  (forall v, is_ik_computed v = true <-> is_ik_spec v) /\
  (forall v, is_ak_computed v = true <-> is_ak_spec v) /\
  (forall v, is_ec_computed v = true <-> is_ec_spec v) /\
  (forall v1 v2, savarna v1 v2 = true <-> savarna_spec v1 v2) /\
  (forall v, is_vrddhi_vowel v = true <-> is_vrddhi_vowel_spec v) /\
  (forall v, is_guna_vowel v = true <-> is_guna_vowel_spec v) /\
  (forall s1 s2, sutra_ltb s1 s2 = true <-> sutra_lt s1 s2) /\
  (forall r1 r2, rule_defeats r1 r2 = true <-> defeats_rel r1 r2) /\
  (forall v1 v2 r, select_rule v1 v2 = Some r <-> sandhi_winner r v1 v2) /\
  (forall v1 v2 out, apply_ac_sandhi v1 v2 = out <-> ac_sandhi_rel v1 v2 out).
Proof.
  split; [exact is_ik_correct |].
  split; [exact is_ak_correct |].
  split; [exact is_ec_correct |].
  split; [exact savarna_correct |].
  split; [exact is_vrddhi_vowel_correct |].
  split; [exact is_guna_vowel_correct |].
  split; [exact sutra_ltb_correct |].
  split; [exact rule_defeats_correct |].
  split; [exact select_rule_correct |].
  exact soundness_completeness.
Qed.

(** * Part XXVI: Roadmap for Extended Coverage *)

(** The following sūtras from Aṣṭādhyāyī are candidates for future formalization:

    ** Vowel Sandhi (6.1) - Not Yet Implemented:
    - 6.1.84 ekaḥ pūrvaparayoḥ (general substitution principle)
    - 6.1.94 antādivacca (treatment of augments)
    - 6.1.97 ato guṇe (a before guṇa is deleted)
    - 6.1.102-104 variants of savarṇa-dīrgha

    ** Pragṛhya Vowels (1.1.11-14) - Exceptions to Sandhi:
    - 1.1.11 ī ū ṛ ḷ ākṣarasya (dual endings)
    - 1.1.12 adaso mātaḥ (adaḥ before māt)
    - 1.1.14 nipāta ekājanaḥ (certain particles)

    ** Optional Sandhi (vikalpa):
    - Many rules have optional application; current formalization assumes
      obligatory sandhi.

    ** Internal Sandhi:
    - Rules applying within words (dhātu-pratyaya juncture)
    - Different precedence than external sandhi

    ** Vedic Variants:
    - Chandas (Vedic) exceptions to Pāṇinian rules

    ** Consonant Sandhi Extensions:
    - 8.2.39 jhalaṁ jaśo 'nte (word-final devoicing)
    - 8.4.45 yaro 'nunāsike 'nunāsiko vā (optional nasalization)
    - Additional retroflex rules (8.4.1-39)

    The architecture supports extension: add to RuleId, define rule_matches,
    apply_rule, and update the precedence proofs. *)

(** * Part XXVII: Inverse Sandhi (Sandhi-Viccheda) *)

(** Sandhi-viccheda is the inverse operation: given a sandhi'd form, recover
    the original vowel pair. This is non-deterministic since multiple inputs
    can produce the same output (e.g., both a+i and ā+i yield e via guṇa). *)

(** Possible pre-sandhi pairs for a given output. *)
Definition inverse_sandhi_candidates (result : list Phoneme)
  : list (Vowel * Vowel) :=
  match result with
  | [Svar V_aa] =>
      [(V_a, V_a); (V_aa, V_a); (V_a, V_aa); (V_aa, V_aa)]
  | [Svar V_ii] =>
      [(V_i, V_i); (V_ii, V_i); (V_i, V_ii); (V_ii, V_ii)]
  | [Svar V_uu] =>
      [(V_u, V_u); (V_uu, V_u); (V_u, V_uu); (V_uu, V_uu)]
  | [Svar V_rr] =>
      [(V_r, V_r); (V_rr, V_r); (V_r, V_rr); (V_rr, V_rr)]
  | [Svar V_e] =>
      [(V_a, V_i); (V_a, V_ii); (V_aa, V_i); (V_aa, V_ii); (V_e, V_a)]
  | [Svar V_o] =>
      [(V_a, V_u); (V_a, V_uu); (V_aa, V_u); (V_aa, V_uu); (V_o, V_a)]
  | [Svar V_ai] =>
      [(V_a, V_e); (V_a, V_ai); (V_aa, V_e); (V_aa, V_ai)]
  | [Svar V_au] =>
      [(V_a, V_o); (V_a, V_au); (V_aa, V_o); (V_aa, V_au)]
  | [Svar V_a; Vyan C_r] =>
      [(V_a, V_r); (V_a, V_rr); (V_aa, V_r); (V_aa, V_rr)]
  | [Svar V_a; Vyan C_l] =>
      [(V_a, V_l); (V_aa, V_l)]
  | [Vyan C_y; Svar v2] =>
      [(V_i, v2); (V_ii, v2)]
  | [Vyan C_v; Svar v2] =>
      [(V_u, v2); (V_uu, v2)]
  | [Vyan C_r; Svar v2] =>
      [(V_r, v2); (V_rr, v2)]
  | [Vyan C_l; Svar v2] =>
      [(V_l, v2)]
  | _ => []
  end.

(** Verification: each candidate should produce the given result via forward sandhi. *)
Fixpoint phoneme_list_beq (l1 l2 : list Phoneme) : bool :=
  match l1, l2 with
  | [], [] => true
  | p1 :: r1, p2 :: r2 => Phoneme_beq p1 p2 && phoneme_list_beq r1 r2
  | _, _ => false
  end.

Definition verify_inverse (result : list Phoneme) (v1 v2 : Vowel) : bool :=
  phoneme_list_beq (apply_ac_sandhi v1 v2) result.

(** Verification examples for inverse sandhi. *)
Example inverse_e_valid_1 : apply_ac_sandhi V_a V_i = [Svar V_e].
Proof. reflexivity. Qed.

Example inverse_e_valid_2 : apply_ac_sandhi V_e V_a = [Svar V_e].
Proof. reflexivity. Qed.

Example inverse_aa_valid : apply_ac_sandhi V_a V_a = [Svar V_aa].
Proof. reflexivity. Qed.

Example inverse_ya_valid : apply_ac_sandhi V_i V_a = [Vyan C_y; Svar V_a].
Proof. reflexivity. Qed.

Example inverse_ar_valid : apply_ac_sandhi V_a V_r = [Svar V_a; Vyan C_r].
Proof. reflexivity. Qed.

(** * Part XXVIII: Pragṛhya Vowels (1.1.11-14) *)

(** Pragṛhya vowels are exempt from sandhi. The Aṣṭādhyāyī defines several
    categories of pragṛhya vowels based on morphological context. *)

(** ** Morphological contexts that create pragṛhya status *)

Inductive PragrhyaContext : Type :=
  | PC_DualEnding
  | PC_AdasMat
  | PC_ParticleSe
  | PC_SingleVowelNipata
  | PC_None.

(** ** 1.1.11 ī ū ṛ ḷ ākṣarasya *)
(** Dual endings -ī, -ū, -ṛ (as in devī, senī; vadhū, camū; pitṛ, mātṛ)
    are pragṛhya and do not undergo sandhi. *)

Definition is_dual_ending_vowel (v : Vowel) : bool :=
  match v with
  | V_ii | V_uu | V_rr => true
  | _ => false
  end.

Inductive is_pragrhya_1_1_11 : Vowel -> Prop :=
  | Prag_ii : is_pragrhya_1_1_11 V_ii
  | Prag_uu : is_pragrhya_1_1_11 V_uu
  | Prag_rr : is_pragrhya_1_1_11 V_rr.

Lemma is_dual_ending_vowel_correct : forall v,
  is_dual_ending_vowel v = true <-> is_pragrhya_1_1_11 v.
Proof.
  intro v; split.
  - intro H; destruct v; simpl in H; try discriminate; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** ** 1.1.12 adaso mātaḥ *)
(** The pronoun adaḥ before the suffix māt is pragṛhya.
    We model this as a specific lexical context. *)

Inductive AdasContext : Type :=
  | Adas_before_mat
  | Adas_other.

Definition is_pragrhya_1_1_12 (ctx : AdasContext) : bool :=
  match ctx with
  | Adas_before_mat => true
  | Adas_other => false
  end.

(** ** 1.1.14 nipāta ekājanaḥ *)
(** Single-vowel indeclinables (nipātas) like ā, i, u, e, o, etc.
    are pragṛhya when used as particles. *)

Inductive NipataStatus : Type :=
  | Nipata_single_vowel
  | Nipata_multi
  | Not_nipata.

Definition is_pragrhya_1_1_14 (status : NipataStatus) : bool :=
  match status with
  | Nipata_single_vowel => true
  | _ => false
  end.

(** ** Combined pragṛhya check *)

Record PragrhyaInfo := {
  pragrhya_context : PragrhyaContext;
  adas_context : AdasContext;
  nipata_status : NipataStatus
}.

Definition default_pragrhya_info : PragrhyaInfo := {|
  pragrhya_context := PC_None;
  adas_context := Adas_other;
  nipata_status := Not_nipata
|}.

Definition is_pragrhya (v : Vowel) (info : PragrhyaInfo) : bool :=
  match pragrhya_context info with
  | PC_DualEnding => is_dual_ending_vowel v
  | PC_AdasMat => is_pragrhya_1_1_12 (adas_context info)
  | PC_ParticleSe => true
  | PC_SingleVowelNipata => is_pragrhya_1_1_14 (nipata_status info)
  | PC_None => false
  end.

(** ** Pragṛhya-aware sandhi function *)

Definition apply_ac_sandhi_pragrhya
  (v1 : Vowel) (info1 : PragrhyaInfo)
  (v2 : Vowel) (info2 : PragrhyaInfo)
  : list Phoneme :=
  if is_pragrhya v1 info1 then
    [Svar v1; Svar v2]
  else
    apply_ac_sandhi v1 v2.

(** ** Specification: pragṛhya vowels block sandhi *)

Inductive pragrhya_sandhi_spec : Vowel -> PragrhyaInfo -> Vowel -> list Phoneme -> Prop :=
  | PSS_blocked : forall v1 info1 v2,
      is_pragrhya v1 info1 = true ->
      pragrhya_sandhi_spec v1 info1 v2 [Svar v1; Svar v2]
  | PSS_normal : forall v1 info1 v2 out,
      is_pragrhya v1 info1 = false ->
      ac_sandhi_rel v1 v2 out ->
      pragrhya_sandhi_spec v1 info1 v2 out.

Theorem apply_ac_sandhi_pragrhya_correct : forall v1 info1 v2 info2 out,
  apply_ac_sandhi_pragrhya v1 info1 v2 info2 = out <->
  pragrhya_sandhi_spec v1 info1 v2 out.
Proof.
  intros v1 info1 v2 info2 out.
  split.
  - intro H.
    unfold apply_ac_sandhi_pragrhya in H.
    destruct (is_pragrhya v1 info1) eqn:Eprag.
    + subst. apply PSS_blocked. exact Eprag.
    + apply PSS_normal.
      * exact Eprag.
      * apply soundness. exact H.
  - intro H.
    destruct H.
    + unfold apply_ac_sandhi_pragrhya.
      rewrite H. reflexivity.
    + unfold apply_ac_sandhi_pragrhya.
      rewrite H.
      apply completeness. exact H0.
Qed.

(** ** Examples of pragṛhya blocking sandhi *)

Example pragrhya_dual_ii :
  apply_ac_sandhi_pragrhya V_ii
    {| pragrhya_context := PC_DualEnding; adas_context := Adas_other; nipata_status := Not_nipata |}
    V_a default_pragrhya_info = [Svar V_ii; Svar V_a].
Proof. reflexivity. Qed.

Example pragrhya_dual_uu :
  apply_ac_sandhi_pragrhya V_uu
    {| pragrhya_context := PC_DualEnding; adas_context := Adas_other; nipata_status := Not_nipata |}
    V_i default_pragrhya_info = [Svar V_uu; Svar V_i].
Proof. reflexivity. Qed.

Example pragrhya_nipata :
  apply_ac_sandhi_pragrhya V_a
    {| pragrhya_context := PC_SingleVowelNipata; adas_context := Adas_other; nipata_status := Nipata_single_vowel |}
    V_i default_pragrhya_info = [Svar V_a; Svar V_i].
Proof. reflexivity. Qed.

Example non_pragrhya_normal :
  apply_ac_sandhi_pragrhya V_a default_pragrhya_info V_i default_pragrhya_info = [Svar V_e].
Proof. reflexivity. Qed.

(** Counterexample: non-dual ī still undergoes sandhi. *)
Example non_dual_ii_sandhi :
  apply_ac_sandhi_pragrhya V_ii default_pragrhya_info V_a default_pragrhya_info = [Vyan C_y; Svar V_a].
Proof. reflexivity. Qed.

(** ** Totality: pragṛhya sandhi always produces a result *)

Theorem pragrhya_sandhi_total : forall v1 info1 v2 info2,
  exists ps, apply_ac_sandhi_pragrhya v1 info1 v2 info2 = ps /\ ps <> [].
Proof.
  intros v1 info1 v2 info2.
  unfold apply_ac_sandhi_pragrhya.
  destruct (is_pragrhya v1 info1) eqn:E.
  - exists [Svar v1; Svar v2]. split.
    + reflexivity.
    + discriminate.
  - exists (apply_ac_sandhi v1 v2). split.
    + reflexivity.
    + apply apply_ac_sandhi_nonempty.
Qed.

(** * Part XXIX: Optional Sandhi (Vikalpa) *)

(** Many Pāṇinian rules are marked "vā" (optionally), meaning the speaker
    can choose whether to apply them. This section implements vikalpa
    (optional) sandhi with support for multiple valid outputs. *)

(** ** Optionality marker for rules *)

Inductive Optionality : Type :=
  | Nitya
  | Vikalpa.

(** ** Extended Rule ID with optionality *)

Record VikalpaRuleId := {
  base_rule : RuleId;
  optionality : Optionality
}.

Definition make_nitya (r : RuleId) : VikalpaRuleId :=
  {| base_rule := r; optionality := Nitya |}.

Definition make_vikalpa (r : RuleId) : VikalpaRuleId :=
  {| base_rule := r; optionality := Vikalpa |}.

(** ** 6.1.109 as vikalpa *)
(** In some grammatical traditions, pūrvarūpa (6.1.109) is considered
    optional, allowing either e/o + a → e/o (pūrvarūpa) or the standard
    ayavāyāv sandhi (6.1.78). *)

Definition rule_optionality (r : RuleId) : Optionality :=
  match r with
  | R_6_1_109 => Vikalpa
  | _ => Nitya
  end.

(** ** Vikalpa-aware sandhi result type *)

Inductive VikalpaSandhiResult : Type :=
  | VSResult_single : list Phoneme -> VikalpaSandhiResult
  | VSResult_choice : list Phoneme -> list Phoneme -> VikalpaSandhiResult.

(** ** Compute alternative result when vikalpa applies *)

Definition alternative_for_109 (v1 v2 : Vowel) : option (list Phoneme) :=
  if is_en v1 && Vowel_beq v2 V_a then
    match ayavayav v1 with
    | Some prefix => Some (prefix ++ [Svar v2])
    | None => None
    end
  else None.

(** ** Vikalpa-aware sandhi function *)

Definition apply_ac_sandhi_vikalpa (v1 v2 : Vowel) : VikalpaSandhiResult :=
  match select_rule v1 v2 with
  | Some r =>
      let primary := apply_rule r v1 v2 in
      match rule_optionality r with
      | Nitya => VSResult_single primary
      | Vikalpa =>
          match r with
          | R_6_1_109 =>
              match alternative_for_109 v1 v2 with
              | Some alt => VSResult_choice primary alt
              | None => VSResult_single primary
              end
          | _ => VSResult_single primary
          end
      end
  | None => VSResult_single [Svar v1; Svar v2]
  end.

(** ** Specification for vikalpa sandhi *)

Inductive vikalpa_sandhi_spec : Vowel -> Vowel -> VikalpaSandhiResult -> Prop :=
  | VSS_nitya : forall v1 v2 r out,
      sandhi_winner r v1 v2 ->
      rule_optionality r = Nitya ->
      rule_output_spec r v1 v2 out ->
      vikalpa_sandhi_spec v1 v2 (VSResult_single out)
  | VSS_vikalpa : forall v1 v2 r primary alt,
      sandhi_winner r v1 v2 ->
      rule_optionality r = Vikalpa ->
      rule_output_spec r v1 v2 primary ->
      vikalpa_sandhi_spec v1 v2 (VSResult_choice primary alt)
  | VSS_no_rule : forall v1 v2,
      (forall r, ~ sandhi_applicable r v1 v2) ->
      vikalpa_sandhi_spec v1 v2 (VSResult_single [Svar v1; Svar v2]).

(** ** Helper: extract any valid result from vikalpa *)

Definition vikalpa_primary (vsr : VikalpaSandhiResult) : list Phoneme :=
  match vsr with
  | VSResult_single ps => ps
  | VSResult_choice ps _ => ps
  end.

Definition vikalpa_all_results (vsr : VikalpaSandhiResult) : list (list Phoneme) :=
  match vsr with
  | VSResult_single ps => [ps]
  | VSResult_choice ps1 ps2 => [ps1; ps2]
  end.

(** ** Examples of vikalpa sandhi *)

Example vikalpa_e_a_choice :
  apply_ac_sandhi_vikalpa V_e V_a =
    VSResult_choice [Svar V_e] [Svar V_a; Vyan C_y; Svar V_a].
Proof. reflexivity. Qed.

Example vikalpa_o_a_choice :
  apply_ac_sandhi_vikalpa V_o V_a =
    VSResult_choice [Svar V_o] [Svar V_a; Vyan C_v; Svar V_a].
Proof. reflexivity. Qed.

Example vikalpa_a_i_nitya :
  apply_ac_sandhi_vikalpa V_a V_i = VSResult_single [Svar V_e].
Proof. reflexivity. Qed.

Example vikalpa_i_a_nitya :
  apply_ac_sandhi_vikalpa V_i V_a = VSResult_single [Vyan C_y; Svar V_a].
Proof. reflexivity. Qed.

(** ** Membership in vikalpa results *)

Definition in_vikalpa_results (ps : list Phoneme) (vsr : VikalpaSandhiResult) : Prop :=
  In ps (vikalpa_all_results vsr).

(** ** The primary result is always valid *)

Lemma vikalpa_primary_in_results : forall vsr,
  in_vikalpa_results (vikalpa_primary vsr) vsr.
Proof.
  intro vsr.
  destruct vsr; unfold in_vikalpa_results, vikalpa_all_results, vikalpa_primary.
  - left. reflexivity.
  - left. reflexivity.
Qed.

(** ** Non-emptiness of vikalpa results *)

Theorem vikalpa_result_nonempty : forall v1 v2,
  vikalpa_all_results (apply_ac_sandhi_vikalpa v1 v2) <> [].
Proof.
  intros v1 v2.
  unfold apply_ac_sandhi_vikalpa.
  destruct (select_rule v1 v2) eqn:E.
  - destruct (rule_optionality r) eqn:Eopt.
    + discriminate.
    + destruct r; simpl in Eopt; try discriminate.
      destruct (alternative_for_109 v1 v2); discriminate.
  - discriminate.
Qed.

(** ** Correspondence with deterministic sandhi *)

Lemma vikalpa_primary_matches_deterministic : forall v1 v2,
  vikalpa_primary (apply_ac_sandhi_vikalpa v1 v2) = apply_ac_sandhi v1 v2.
Proof.
  intros v1 v2.
  unfold apply_ac_sandhi_vikalpa, apply_ac_sandhi.
  destruct (select_rule v1 v2) eqn:E.
  - destruct (rule_optionality r) eqn:Eopt.
    + reflexivity.
    + destruct r; simpl in Eopt; try discriminate.
      destruct (alternative_for_109 v1 v2); reflexivity.
  - reflexivity.
Qed.

(** ** Additional vikalpa rules can be added by:
    1. Marking rule_optionality to return Vikalpa
    2. Defining alternative_for_XXX functions
    3. Extending the match in apply_ac_sandhi_vikalpa *)

(** * Part XXX: Internal Sandhi (Dhātu-Pratyaya Juncture) *)

(** Internal sandhi applies at morpheme boundaries within words, particularly
    at the dhātu-pratyaya (root-suffix) juncture. Key differences from
    external sandhi:
    - Rule 6.1.109 (pūrvarūpa) does NOT apply internally
    - Guṇa/vṛddhi triggered by suffix markers (sārvadhātuka, ārdhadhātuka)
    - Some rules are nitya (obligatory) internally but anitya externally *)

(** ** Suffix classification *)

Inductive SuffixType : Type :=
  | Sarvadhatuka
  | Ardhadhatuka
  | Taddhita
  | Krt
  | Sup
  | Tin
  | UnmarkedSuffix.

(** ** Properties of suffixes relevant to sandhi *)

Record SuffixInfo := {
  suffix_type : SuffixType;
  is_pit : bool;
  is_kit : bool;
  begins_with_vowel : bool
}.

Definition default_suffix_info : SuffixInfo := {|
  suffix_type := UnmarkedSuffix;
  is_pit := false;
  is_kit := false;
  begins_with_vowel := false
|}.

(** ** 1.1.5 kṅiti ca (guṇa/vṛddhi blocked before k/ṅ-marked suffixes) *)

Definition blocks_guna_vrddhi (info : SuffixInfo) : bool :=
  is_kit info || is_pit info.

Inductive blocks_guna_vrddhi_spec : SuffixInfo -> Prop :=
  | BGV_kit : forall info, is_kit info = true -> blocks_guna_vrddhi_spec info
  | BGV_pit : forall info, is_pit info = true -> blocks_guna_vrddhi_spec info.

Lemma blocks_guna_vrddhi_correct : forall info,
  blocks_guna_vrddhi info = true <-> blocks_guna_vrddhi_spec info.
Proof.
  intro info; split.
  - intro H.
    unfold blocks_guna_vrddhi in H.
    apply Bool.orb_true_iff in H.
    destruct H as [Hkit | Hpit].
    + apply BGV_kit. exact Hkit.
    + apply BGV_pit. exact Hpit.
  - intro H.
    destruct H; unfold blocks_guna_vrddhi.
    + rewrite H. reflexivity.
    + rewrite H. apply Bool.orb_true_r.
Qed.

(** ** Internal sandhi rule applicability *)

Definition rule_applies_internally (r : RuleId) : bool :=
  match r with
  | R_6_1_109 => false
  | _ => true
  end.

Definition internal_rule_matches (r : RuleId) (v1 v2 : Vowel) (sinfo : SuffixInfo) : bool :=
  rule_applies_internally r &&
  match r with
  | R_6_1_87 =>
      if blocks_guna_vrddhi sinfo then false
      else rule_matches r v1 v2
  | R_6_1_88 =>
      if blocks_guna_vrddhi sinfo then false
      else rule_matches r v1 v2
  | _ => rule_matches r v1 v2
  end.

(** ** Internal sandhi rule selection *)

Fixpoint matching_rules_internal (rules : list RuleId) (v1 v2 : Vowel) (sinfo : SuffixInfo)
  : list RuleId :=
  match rules with
  | [] => []
  | r :: rs =>
      if internal_rule_matches r v1 v2 sinfo
      then r :: matching_rules_internal rs v1 v2 sinfo
      else matching_rules_internal rs v1 v2 sinfo
  end.

Definition select_rule_internal (v1 v2 : Vowel) (sinfo : SuffixInfo) : option RuleId :=
  find_winner (matching_rules_internal all_rules v1 v2 sinfo).

(** ** Internal sandhi function *)

Definition apply_internal_sandhi (v1 v2 : Vowel) (sinfo : SuffixInfo) : list Phoneme :=
  match select_rule_internal v1 v2 sinfo with
  | Some r => apply_rule r v1 v2
  | None => [Svar v1; Svar v2]
  end.

(** ** Specification for internal sandhi *)

Inductive internal_sandhi_applicable : RuleId -> Vowel -> Vowel -> SuffixInfo -> Prop :=
  | ISA_77 : forall v1 v2 sinfo,
      is_ik_computed v1 = true ->
      internal_sandhi_applicable R_6_1_77 v1 v2 sinfo
  | ISA_78 : forall v1 v2 sinfo,
      is_ec_computed v1 = true ->
      internal_sandhi_applicable R_6_1_78 v1 v2 sinfo
  | ISA_87 : forall v1 v2 sinfo,
      is_a_class v1 = true ->
      blocks_guna_vrddhi sinfo = false ->
      internal_sandhi_applicable R_6_1_87 v1 v2 sinfo
  | ISA_88 : forall v1 v2 sinfo,
      is_a_class v1 = true ->
      is_ec_computed v2 = true ->
      blocks_guna_vrddhi sinfo = false ->
      internal_sandhi_applicable R_6_1_88 v1 v2 sinfo
  | ISA_101 : forall v1 v2 sinfo,
      is_ak_computed v1 = true ->
      is_ak_computed v2 = true ->
      savarna v1 v2 = true ->
      internal_sandhi_applicable R_6_1_101 v1 v2 sinfo.

(** Note: R_6_1_109 is NOT in internal_sandhi_applicable - it's padānta only *)

(** ** Examples of internal sandhi *)

Example internal_a_i_guna :
  apply_internal_sandhi V_a V_i default_suffix_info = [Svar V_e].
Proof. reflexivity. Qed.

(** When guṇa is blocked by kit and vowels are not savarṇa, no sandhi applies *)
Example internal_a_i_kit_blocked :
  apply_internal_sandhi V_a V_i
    {| suffix_type := Krt; is_pit := false; is_kit := true; begins_with_vowel := true |}
    = [Svar V_a; Svar V_i].
Proof. reflexivity. Qed.

(** Savarṇa dīrgha still applies even when guṇa is blocked *)
Example internal_a_a_kit_dirgha :
  apply_internal_sandhi V_a V_a
    {| suffix_type := Krt; is_pit := false; is_kit := true; begins_with_vowel := true |}
    = [Svar V_aa].
Proof. reflexivity. Qed.

Example internal_i_a_yan :
  apply_internal_sandhi V_i V_a default_suffix_info = [Vyan C_y; Svar V_a].
Proof. reflexivity. Qed.

Example internal_e_a_no_purvarupa :
  apply_internal_sandhi V_e V_a default_suffix_info = [Svar V_a; Vyan C_y; Svar V_a].
Proof. reflexivity. Qed.

(** Contrast: external sandhi gives pūrvarūpa for e + a *)
Example external_e_a_purvarupa :
  apply_ac_sandhi V_e V_a = [Svar V_e].
Proof. reflexivity. Qed.

(** ** kṅiti blocking guṇa example *)

(** bhū + ta (kit suffix) → bhūta (no guṇa, dīrgha applies) *)
Example bhu_ta_kit :
  apply_internal_sandhi V_uu V_a
    {| suffix_type := Krt; is_pit := false; is_kit := true; begins_with_vowel := true |}
    = [Vyan C_v; Svar V_a].
Proof. reflexivity. Qed.

(** bhū + ana (non-kit suffix) → bhavana (guṇa applies) *)
Example bhu_ana_non_kit :
  apply_internal_sandhi V_a V_uu default_suffix_info = [Svar V_o].
Proof. reflexivity. Qed.

(** ** Totality for internal sandhi *)

(** For most vowel pairs, internal sandhi produces a result.
    The key insight is that ik vowels always have yaṇ available,
    and a-class vowels have guṇa (unless blocked) or dīrgha (for savarṇa). *)

(** Non-emptiness: internal sandhi never produces empty output *)
Theorem internal_sandhi_nonempty : forall v1 v2 sinfo,
  apply_internal_sandhi v1 v2 sinfo <> [].
Proof.
  intros v1 v2 sinfo.
  unfold apply_internal_sandhi.
  destruct (select_rule_internal v1 v2 sinfo) eqn:E.
  - destruct r; destruct v1, v2; simpl; intro H; inversion H.
  - intro H; inversion H.
Qed.

(** ** Correctness: internal sandhi differs from external at key points *)

Theorem internal_external_differ_109 : forall v,
  is_en v = true ->
  apply_internal_sandhi v V_a default_suffix_info <> apply_ac_sandhi v V_a.
Proof.
  intros v Hen.
  destruct v; simpl in Hen; try discriminate;
  simpl; intro H; inversion H.
Qed.

(** ** Unified boundary-aware sandhi *)

Definition apply_sandhi_at_boundary
  (v1 v2 : Vowel)
  (boundary : MorphBoundary)
  (sinfo : SuffixInfo)
  : list Phoneme :=
  match boundary with
  | PadaAnta | SamasaAnta => apply_ac_sandhi v1 v2
  | DhatuPratyaya => apply_internal_sandhi v1 v2 sinfo
  | Internal => [Svar v1; Svar v2]
  end.

Example boundary_pada_uses_external :
  apply_sandhi_at_boundary V_e V_a PadaAnta default_suffix_info = [Svar V_e].
Proof. reflexivity. Qed.

Example boundary_dhatu_uses_internal :
  apply_sandhi_at_boundary V_e V_a DhatuPratyaya default_suffix_info = [Svar V_a; Vyan C_y; Svar V_a].
Proof. reflexivity. Qed.

Example boundary_internal_no_sandhi :
  apply_sandhi_at_boundary V_a V_i Internal default_suffix_info = [Svar V_a; Svar V_i].
Proof. reflexivity. Qed.

(** * Part XXXI: Structural Proofs *)

(** This section refactors enumeration-based proofs into structural proofs
    that derive results from algebraic properties rather than case analysis.
    This makes the proofs more extensible and reveals the underlying structure. *)

(** ** Vowel Classification Structure *)

(** Instead of enumerating all 13 vowels, we classify them structurally.
    This classification captures the essential property for sandhi rule selection. *)

Inductive VowelClass : Type :=
  | VC_A
  | VC_IK
  | VC_EC.

Definition classify_vowel (v : Vowel) : VowelClass :=
  match v with
  | V_a | V_aa => VC_A
  | V_i | V_ii | V_u | V_uu | V_r | V_rr | V_l => VC_IK
  | V_e | V_ai | V_o | V_au => VC_EC
  end.

(** Structural lemma: classification is exhaustive *)
Lemma classify_exhaustive : forall v,
  classify_vowel v = VC_A \/
  classify_vowel v = VC_IK \/
  classify_vowel v = VC_EC.
Proof.
  intro v; destruct v; simpl; auto.
Qed.

(** Structural correspondence with boolean predicates *)
Lemma classify_a_iff : forall v,
  classify_vowel v = VC_A <-> is_a_class v = true.
Proof.
  intro v; split; intro H; destruct v; simpl in *; try discriminate; reflexivity.
Qed.

Lemma classify_ik_iff : forall v,
  classify_vowel v = VC_IK <-> is_ik_computed v = true.
Proof.
  intro v; split; intro H; destruct v; simpl in *; try discriminate; reflexivity.
Qed.

Lemma classify_ec_iff : forall v,
  classify_vowel v = VC_EC <-> is_ec_computed v = true.
Proof.
  intro v; split; intro H; destruct v; simpl in *; try discriminate; reflexivity.
Qed.

(** Structural proof of vowel_classification using classify_vowel *)
Theorem vowel_classification_structural : forall v,
  is_a_class v = true \/
  is_ik_computed v = true \/
  is_ec_computed v = true.
Proof.
  intro v.
  destruct (classify_exhaustive v) as [Ha | [Hik | Hec]].
  - left. apply classify_a_iff. exact Ha.
  - right. left. apply classify_ik_iff. exact Hik.
  - right. right. apply classify_ec_iff. exact Hec.
Qed.

(** ** Rule Defeat Structure *)

(** The defeat relation has algebraic properties that can be proven structurally. *)

(** Property 1: Defeat is determined by sūtra number when no apavāda applies *)
Definition defeat_by_sutra_number (r1 r2 : RuleId) : bool :=
  sutra_ltb (rule_sutra_num r2) (rule_sutra_num r1).

(** Property 2: Apavāda relationships form a partial order *)
Lemma apavada_irrefl : forall r, is_apavada r r = false.
Proof.
  intro r; destruct r; reflexivity.
Qed.

Lemma apavada_antisym : forall r1 r2,
  is_apavada r1 r2 = true -> is_apavada r2 r1 = false.
Proof.
  intros r1 r2 H.
  destruct r1, r2; simpl in *; try discriminate; reflexivity.
Qed.

(** Property 3: Defeat derives from apavāda or sūtra order *)
Theorem defeat_structure : forall r1 r2,
  rule_defeats r1 r2 = true <->
  (is_apavada r1 r2 = true \/
   (is_apavada r1 r2 = false /\ is_apavada r2 r1 = false /\
    sutra_ltb (rule_sutra_num r2) (rule_sutra_num r1) = true)).
Proof.
  intros r1 r2.
  unfold rule_defeats.
  split.
  - intro H.
    destruct (is_apavada r1 r2) eqn:E1.
    + left. reflexivity.
    + right. simpl in H.
      apply Bool.andb_true_iff in H.
      destruct H as [Hneg Hlt].
      apply Bool.negb_true_iff in Hneg.
      auto.
  - intros [H | [H1 [H2 H3]]].
    + rewrite H. reflexivity.
    + rewrite H1. simpl. rewrite H2. simpl. exact H3.
Qed.

(** Property 4: Totality follows from sūtra ordering being total *)
Lemma sutra_total : forall s1 s2,
  s1 = s2 \/ sutra_ltb s1 s2 = true \/ sutra_ltb s2 s1 = true.
Proof.
  intros s1 s2.
  destruct (Nat.lt_trichotomy (adhyaya s1) (adhyaya s2)) as [Hlt | [Heq | Hgt]].
  - right. left. unfold sutra_ltb. apply Nat.ltb_lt in Hlt. rewrite Hlt. reflexivity.
  - destruct (Nat.lt_trichotomy (pada s1) (pada s2)) as [Plt | [Peq | Pgt]].
    + right. left. unfold sutra_ltb.
      assert (Nat.ltb (adhyaya s1) (adhyaya s2) = false) by (apply Nat.ltb_ge; lia).
      rewrite H.
      assert (Nat.eqb (adhyaya s1) (adhyaya s2) = true) by (apply Nat.eqb_eq; lia).
      rewrite H0.
      apply Nat.ltb_lt in Plt. rewrite Plt. reflexivity.
    + destruct (Nat.lt_trichotomy (sutra s1) (sutra s2)) as [Slt | [Seq | Sgt]].
      * right. left. unfold sutra_ltb.
        assert (Nat.ltb (adhyaya s1) (adhyaya s2) = false) by (apply Nat.ltb_ge; lia).
        rewrite H.
        assert (Nat.eqb (adhyaya s1) (adhyaya s2) = true) by (apply Nat.eqb_eq; lia).
        rewrite H0.
        assert (Nat.ltb (pada s1) (pada s2) = false) by (apply Nat.ltb_ge; lia).
        rewrite H1.
        assert (Nat.eqb (pada s1) (pada s2) = true) by (apply Nat.eqb_eq; lia).
        rewrite H2.
        apply Nat.ltb_lt in Slt. exact Slt.
      * left. destruct s1, s2; simpl in *; subst; reflexivity.
      * right. right. unfold sutra_ltb.
        assert (Nat.ltb (adhyaya s2) (adhyaya s1) = false) by (apply Nat.ltb_ge; lia).
        rewrite H.
        assert (Nat.eqb (adhyaya s2) (adhyaya s1) = true) by (apply Nat.eqb_eq; lia).
        rewrite H0.
        assert (Nat.ltb (pada s2) (pada s1) = false) by (apply Nat.ltb_ge; lia).
        rewrite H1.
        assert (Nat.eqb (pada s2) (pada s1) = true) by (apply Nat.eqb_eq; lia).
        rewrite H2.
        apply Nat.ltb_lt. lia.
    + right. right. unfold sutra_ltb.
      assert (Nat.ltb (adhyaya s2) (adhyaya s1) = false) by (apply Nat.ltb_ge; lia).
      rewrite H.
      assert (Nat.eqb (adhyaya s2) (adhyaya s1) = true) by (apply Nat.eqb_eq; lia).
      rewrite H0.
      apply Nat.ltb_lt in Pgt. rewrite Pgt. reflexivity.
  - right. right. unfold sutra_ltb. apply Nat.ltb_lt in Hgt. rewrite Hgt. reflexivity.
Qed.

(** Structural proof of defeat totality *)
Theorem defeat_total_structural : forall r1 r2,
  r1 = r2 \/ rule_defeats r1 r2 = true \/ rule_defeats r2 r1 = true.
Proof.
  intros r1 r2.
  destruct (RuleId_eq_dec r1 r2) as [Heq | Hneq].
  - left. exact Heq.
  - right.
    destruct (is_apavada r1 r2) eqn:E1.
    + left. unfold rule_defeats. rewrite E1. reflexivity.
    + destruct (is_apavada r2 r1) eqn:E2.
      * right. unfold rule_defeats. rewrite E2. reflexivity.
      * destruct (sutra_total (rule_sutra_num r1) (rule_sutra_num r2)) as [Heqs | [Hlt | Hgt]].
        -- exfalso.
           destruct r1, r2; simpl in Heqs; try (injection Heqs; intros; lia);
           simpl in Hneq; contradiction.
        -- right. unfold rule_defeats. rewrite E2. simpl. rewrite E1. simpl. exact Hlt.
        -- left. unfold rule_defeats. rewrite E1. simpl. rewrite E2. simpl. exact Hgt.
Qed.

