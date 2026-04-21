theory Angelic_Processes
  imports "UTP2.utp"
begin

declare [[quick_and_dirty = true]]

text \<open>
  Roadmap formalisation for Pedro Ribeiro's dissertation \<^emph>\<open>Angelic Processes\<close>.

  This file deliberately states the main definitions and proof obligations without
  proving them.  The goal is to freeze a first Isabelle-facing map of the thesis:
  extended binary multirelations, angelic designs, reactive angelic designs, and
  angelic processes.  Proofs are left as \<open>sorry\<close> so that later autoformalisation
  passes can attack one small lemma at a time using \<open>eval_at\<close>, Sledgehammer, and
  \<open>desorry\<close>.

  The definitions below are a conservative shallow model.  They are not yet the
  final polished Isabelle/UTP embedding of all observational variables, but they
  give typed names for the dissertation's healthiness conditions, linking maps,
  operators, Galois connections, and headline algebraic laws.
\<close>

section \<open>Extended Binary Multirelations\<close>

datatype 's ap_ext_state = AP_Nonterm | AP_Term 's

type_synonym 's ap_bmb = "('s \<times> 's ap_ext_state set) set"
type_synonym 's ap_bm = "('s \<times> 's set) set"

definition ap_has_nonterm :: "'s ap_ext_state set \<Rightarrow> bool" where
  "ap_has_nonterm X \<longleftrightarrow> AP_Nonterm \<in> X"

definition ap_term_image :: "'s set \<Rightarrow> 's ap_ext_state set" where
  "ap_term_image X = AP_Term ` X"

definition ap_term_part :: "'s ap_ext_state set \<Rightarrow> 's set" where
  "ap_term_part X = {s. AP_Term s \<in> X}"

definition ap_BMH0 :: "'s ap_bmb \<Rightarrow> bool" where
  "ap_BMH0 B \<longleftrightarrow>
    (\<forall>s X Y. (s, X) \<in> B \<and> X \<subseteq> Y \<and> (AP_Nonterm \<in> X \<longleftrightarrow> AP_Nonterm \<in> Y)
      \<longrightarrow> (s, Y) \<in> B)"

definition ap_BMH1 :: "'s ap_bmb \<Rightarrow> bool" where
  "ap_BMH1 B \<longleftrightarrow>
    (\<forall>s X. (s, insert AP_Nonterm X) \<in> B \<longrightarrow> (s, X - {AP_Nonterm}) \<in> B)"

definition ap_BMH2 :: "'s ap_bmb \<Rightarrow> bool" where
  "ap_BMH2 B \<longleftrightarrow> (\<forall>s. (s, {}) \<in> B \<longleftrightarrow> (s, {AP_Nonterm}) \<in> B)"

definition ap_BMH3 :: "'s ap_bmb \<Rightarrow> bool" where
  "ap_BMH3 B \<longleftrightarrow>
    (\<forall>s X. (s, {}) \<notin> B \<and> (s, X) \<in> B \<longrightarrow> AP_Nonterm \<notin> X)"

definition ap_BMH_bot :: "'s ap_bmb \<Rightarrow> bool" where
  "ap_BMH_bot B \<longleftrightarrow> ap_BMH0 B \<and> ap_BMH1 B \<and> ap_BMH2 B"

definition ap_BMH_orig_subset :: "'s ap_bmb \<Rightarrow> bool" where
  "ap_BMH_orig_subset B \<longleftrightarrow> ap_BMH_bot B \<and> ap_BMH3 B"

definition ap_bmh0 :: "'s ap_bmb \<Rightarrow> 's ap_bmb" where
  "ap_bmh0 B =
    {(s, Y). \<exists>X. (s, X) \<in> B \<and> X \<subseteq> Y \<and>
      (AP_Nonterm \<in> X \<longleftrightarrow> AP_Nonterm \<in> Y)}"

definition ap_bmh1 :: "'s ap_bmb \<Rightarrow> 's ap_bmb" where
  "ap_bmh1 B = {(s, X). (s, X) \<in> B \<or> (s, insert AP_Nonterm X) \<in> B}"

definition ap_bmh2 :: "'s ap_bmb \<Rightarrow> 's ap_bmb" where
  "ap_bmh2 B = {(s, X). (s, X) \<in> B \<and> ((s, {}) \<in> B \<longleftrightarrow> (s, {AP_Nonterm}) \<in> B)}"

definition ap_bmh3 :: "'s ap_bmb \<Rightarrow> 's ap_bmb" where
  "ap_bmh3 B = {(s, X). (s, X) \<in> B \<and> ((s, {}) \<in> B \<or> AP_Nonterm \<notin> X)}"

definition ap_bmh012 :: "'s ap_bmb \<Rightarrow> 's ap_bmb" where
  "ap_bmh012 B = ap_bmh0 (ap_bmh1 (ap_bmh2 B))"

definition ap_bmh0132 :: "'s ap_bmb \<Rightarrow> 's ap_bmb" where
  "ap_bmh0132 B = ap_bmh0 (ap_bmh1 (ap_bmh3 (ap_bmh2 B)))"

definition ap_bmb_refines :: "'s ap_bmb \<Rightarrow> 's ap_bmb \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>B\<^sub>M\<^sub>\<bottom>" 50) where
  "B1 \<sqsubseteq>\<^sub>B\<^sub>M\<^sub>\<bottom> B0 \<longleftrightarrow> B1 \<supseteq> B0"

definition ap_bmb_miracle :: "'s ap_bmb" where
  "ap_bmb_miracle = {}"

definition ap_bmb_abort :: "'s ap_bmb" where
  "ap_bmb_abort = UNIV"

definition ap_bmb_angelic :: "'s ap_bmb \<Rightarrow> 's ap_bmb \<Rightarrow> 's ap_bmb" (infixl "\<squnion>\<^sub>B\<^sub>M\<^sub>\<bottom>" 65) where
  "B \<squnion>\<^sub>B\<^sub>M\<^sub>\<bottom> C = B \<inter> C"

definition ap_bmb_demonic :: "'s ap_bmb \<Rightarrow> 's ap_bmb \<Rightarrow> 's ap_bmb" (infixl "\<sqinter>\<^sub>B\<^sub>M\<^sub>\<bottom>" 60) where
  "B \<sqinter>\<^sub>B\<^sub>M\<^sub>\<bottom> C = B \<union> C"

definition ap_bmb_seq :: "'s ap_bmb \<Rightarrow> 's ap_bmb \<Rightarrow> 's ap_bmb" (infixl ";\<^sub>B\<^sub>M\<^sub>\<bottom>" 70) where
  "B ;\<^sub>B\<^sub>M\<^sub>\<bottom> C =
    {(s, Z). \<exists>X. (s, X) \<in> B \<and>
      ((AP_Nonterm \<in> X \<and> AP_Nonterm \<in> Z) \<or> AP_Nonterm \<notin> X) \<and>
      (\<forall>t. AP_Term t \<in> X \<longrightarrow> (t, Z) \<in> C)}"

definition ap_bmb2bm :: "'s ap_bmb \<Rightarrow> 's ap_bm" where
  "ap_bmb2bm B = {(s, X). (s, ap_term_image X) \<in> B}"

definition ap_bm2bmb :: "'s ap_bm \<Rightarrow> 's ap_bmb" where
  "ap_bm2bmb R = {(s, X). (s, ap_term_part X) \<in> R \<and> AP_Nonterm \<notin> X}"

lemma ap_BMH0_fixed_point_iff:
  "ap_BMH0 B \<longleftrightarrow> ap_bmh0 B = B"
  sorry

lemma ap_BMH1_fixed_point_iff:
  "ap_BMH1 B \<longleftrightarrow> ap_bmh1 B = B"
  sorry

lemma ap_BMH2_fixed_point_iff:
  "ap_BMH2 B \<longleftrightarrow> ap_bmh2 B = B"
  sorry

lemma ap_BMH3_fixed_point_iff:
  "ap_BMH3 B \<longleftrightarrow> ap_bmh3 B = B"
  sorry

lemma ap_bmh0_idem: "ap_bmh0 (ap_bmh0 B) = ap_bmh0 B"
  sorry

lemma ap_bmh1_idem: "ap_bmh1 (ap_bmh1 B) = ap_bmh1 B"
  sorry

lemma ap_bmh2_idem: "ap_bmh2 (ap_bmh2 B) = ap_bmh2 B"
  sorry

lemma ap_bmh3_idem: "ap_bmh3 (ap_bmh3 B) = ap_bmh3 B"
  sorry

lemma ap_bmh012_characterisation:
  "ap_BMH_bot B \<longleftrightarrow> ap_bmh012 B = B"
  sorry

lemma ap_bmh0132_characterisation:
  "ap_BMH_orig_subset B \<longleftrightarrow> ap_bmh0132 B = B"
  sorry

lemma ap_bmb_angelic_closed:
  assumes "ap_BMH_bot B" "ap_BMH_bot C"
  shows "ap_BMH_bot (B \<squnion>\<^sub>B\<^sub>M\<^sub>\<bottom> C)"
  sorry

lemma ap_bmb_demonic_closed:
  assumes "ap_BMH_bot B" "ap_BMH_bot C"
  shows "ap_BMH_bot (B \<sqinter>\<^sub>B\<^sub>M\<^sub>\<bottom> C)"
  sorry

lemma ap_bmb_seq_closed:
  assumes "ap_BMH_bot B" "ap_BMH_bot C"
  shows "ap_BMH_bot (B ;\<^sub>B\<^sub>M\<^sub>\<bottom> C)"
  sorry

lemma ap_bm_bmb_left_inverse:
  assumes "ap_BMH_orig_subset B"
  shows "ap_bm2bmb (ap_bmb2bm B) = B"
  sorry

lemma ap_bm_bmb_right_inverse:
  "ap_bmb2bm (ap_bm2bmb R) = R"
  sorry

theorem ap_bm_bmb_iso:
  assumes "ap_BMH_orig_subset B"
  shows "ap_bm2bmb (ap_bmb2bm B) = B \<and> ap_bmb2bm (ap_bm2bmb R) = R"
  sorry

section \<open>Angelic Designs\<close>

record 's ap_ades_alpha =
  ap_ok :: bool
  ap_ok' :: bool
  ap_s :: 's
  ap_ac' :: "'s set"

type_synonym 's ap_ades_pred = "'s ap_ades_alpha \<Rightarrow> bool"

definition ap_PBMH :: "'s ap_ades_pred \<Rightarrow> 's ap_ades_pred" where
  "ap_PBMH P = (\<lambda>st. \<exists>A \<subseteq> ap_ac' st. P (st\<lparr>ap_ac' := A\<rparr>))"

definition ap_design :: "'s ap_ades_pred \<Rightarrow> 's ap_ades_pred \<Rightarrow> 's ap_ades_pred" (infixr "\<turnstile>\<^sub>A" 25) where
  "ap_design P Q = (\<lambda>st. (ap_ok st \<and> P st) \<longrightarrow> (ap_ok' st \<and> Q st))"

definition ap_H1 :: "'s ap_ades_pred \<Rightarrow> 's ap_ades_pred" where
  "ap_H1 P = (\<lambda>st. ap_ok st \<longrightarrow> P st)"

definition ap_H2 :: "'s ap_ades_pred \<Rightarrow> 's ap_ades_pred" where
  "ap_H2 P = (\<lambda>st. P (st\<lparr>ap_ok' := False\<rparr>) \<or> (ap_ok' st \<and> P st))"

definition ap_A0 :: "'s ap_ades_pred \<Rightarrow> 's ap_ades_pred" where
  "ap_A0 P = (\<lambda>st.
    P st \<and>
    ((ap_ok st \<and> \<not> P (st\<lparr>ap_ok' := False\<rparr>)) \<longrightarrow>
      (ap_ok' st \<longrightarrow> ap_ac' st \<noteq> {})))"

definition ap_A1 :: "'s ap_ades_pred \<Rightarrow> 's ap_ades_pred" where
  "ap_A1 P =
    ((\<lambda>st. \<not> ap_PBMH (\<lambda>st'. P (st'\<lparr>ap_ok' := False\<rparr>)) st) \<turnstile>\<^sub>A
      ap_PBMH (\<lambda>st. P (st\<lparr>ap_ok' := True\<rparr>)))"

definition ap_A :: "'s ap_ades_pred \<Rightarrow> 's ap_ades_pred" where
  "ap_A P = ap_A0 (ap_A1 P)"

definition ap_seqA :: "'s ap_ades_pred \<Rightarrow> 's ap_ades_pred \<Rightarrow> 's ap_ades_pred" (infixl ";\<^sub>A" 70) where
  "P ;\<^sub>A Q = (\<lambda>st. P (st\<lparr>ap_ac' := {z. Q (st\<lparr>ap_s := z\<rparr>)}\<rparr>))"

definition ap_seqD :: "'s ap_ades_pred \<Rightarrow> 's ap_ades_pred \<Rightarrow> 's ap_ades_pred" (infixl ";\<^sub>D\<^sub>a\<^sub>c" 70) where
  "P ;\<^sub>D\<^sub>a\<^sub>c Q = (\<lambda>st. \<exists>ok0.
    P (st\<lparr>ap_ok' := ok0,
           ap_ac' := {z. Q (st\<lparr>ap_ok := ok0, ap_s := z\<rparr>)}\<rparr>))"

definition ap_A2 :: "'s ap_ades_pred \<Rightarrow> 's ap_ades_pred" where
  "ap_A2 P = (\<lambda>st.
    P (st\<lparr>ap_ac' := {}\<rparr>) \<or>
    (\<exists>y \<in> ap_ac' st. P (st\<lparr>ap_ac' := {y}\<rparr>)))"

definition ap_ad_angelic :: "'s ap_ades_pred \<Rightarrow> 's ap_ades_pred \<Rightarrow> 's ap_ades_pred" (infixl "\<squnion>\<^sub>A\<^sub>D" 65) where
  "P \<squnion>\<^sub>A\<^sub>D Q = (\<lambda>st. P st \<and> Q st)"

definition ap_ad_demonic :: "'s ap_ades_pred \<Rightarrow> 's ap_ades_pred \<Rightarrow> 's ap_ades_pred" (infixl "\<sqinter>\<^sub>A\<^sub>D" 60) where
  "P \<sqinter>\<^sub>A\<^sub>D Q = (\<lambda>st. P st \<or> Q st)"

definition ap_d2bmb :: "'s ap_ades_pred \<Rightarrow> 's ap_bmb" where
  "ap_d2bmb P = {(s, X). P \<lparr>ap_ok = True, ap_ok' = AP_Nonterm \<notin> X,
    ap_s = s, ap_ac' = ap_term_part X\<rparr>}"

definition ap_bmb2d :: "'s ap_bmb \<Rightarrow> 's ap_ades_pred" where
  "ap_bmb2d B = (\<lambda>st.
    (ap_s st, (if ap_ok' st then ap_term_image (ap_ac' st)
      else insert AP_Nonterm (ap_term_image (ap_ac' st)))) \<in> B)"

definition ap_d2ac :: "'s ap_ades_pred \<Rightarrow> 's ap_ades_pred" where
  "ap_d2ac P = ap_A P"

definition ap_ac2p :: "'s ap_ades_pred \<Rightarrow> 's ap_ades_pred" where
  "ap_ac2p P = (\<lambda>st. P (st\<lparr>ap_ac' := {ap_s st}\<rparr>))"

definition ap_d2pbmh :: "'s ap_ades_pred \<Rightarrow> 's ap_ades_pred" where
  "ap_d2pbmh P = ap_PBMH P"

definition ap_pbmh2d :: "'s ap_ades_pred \<Rightarrow> 's ap_ades_pred" where
  "ap_pbmh2d P = ap_A P"

lemma ap_PBMH_idem: "ap_PBMH (ap_PBMH P) = ap_PBMH P"
  sorry

lemma ap_PBMH_mono:
  assumes "P \<le> Q"
  shows "ap_PBMH P \<le> ap_PBMH Q"
  sorry

lemma ap_A0_idem: "ap_A0 (ap_A0 P) = ap_A0 P"
  sorry

lemma ap_A1_idem: "ap_A1 (ap_A1 P) = ap_A1 P"
  sorry

lemma ap_A_idem: "ap_A (ap_A P) = ap_A P"
  sorry

lemma ap_A2_expand:
  "ap_A2 P = (\<lambda>st.
    P (st\<lparr>ap_ac' := {}\<rparr>) \<or> (\<exists>y. y \<in> ap_ac' st \<and> P (st\<lparr>ap_ac' := {y}\<rparr>)))"
  sorry

lemma ap_A0_design_strengthens_post:
  "ap_A0 (P \<turnstile>\<^sub>A Q) = (P \<turnstile>\<^sub>A (\<lambda>st. Q st \<and> ap_ac' st \<noteq> {}))"
  sorry

lemma ap_A1_is_PBMH: "ap_A1 P = ap_PBMH P"
  sorry

lemma ap_A_design_normal_form:
  "ap_A P =
    ap_A0 ((\<lambda>st. \<not> ap_PBMH (\<lambda>st'. P (st'\<lparr>ap_ok' := False\<rparr>)) st) \<turnstile>\<^sub>A
      ap_PBMH (\<lambda>st. P (st\<lparr>ap_ok' := True\<rparr>)))"
  sorry

lemma ap_A_seq_closed:
  assumes "ap_A P = P" "ap_A Q = Q"
  shows "ap_A (P ;\<^sub>D\<^sub>a\<^sub>c Q) = P ;\<^sub>D\<^sub>a\<^sub>c Q"
  sorry

lemma ap_A_angelic_closed:
  assumes "ap_A P = P" "ap_A Q = Q"
  shows "ap_A (P \<squnion>\<^sub>A\<^sub>D Q) = P \<squnion>\<^sub>A\<^sub>D Q"
  sorry

lemma ap_A_demonic_closed:
  assumes "ap_A P = P" "ap_A Q = Q"
  shows "ap_A (P \<sqinter>\<^sub>A\<^sub>D Q) = P \<sqinter>\<^sub>A\<^sub>D Q"
  sorry

theorem ap_d2bmb_bmb2d_iso:
  assumes "ap_A P = P" "ap_BMH_bot B"
  shows "ap_bmb2d (ap_d2bmb P) = P \<and> ap_d2bmb (ap_bmb2d B) = B"
  sorry

theorem ap_d2ac_ac2p_galois:
  "(ap_d2ac P \<le> Q) \<longleftrightarrow> (P \<le> ap_ac2p Q)"
  sorry

theorem ap_d2pbmh_pbmh2d_iso:
  assumes "ap_PBMH P = P" "ap_A Q = Q"
  shows "ap_d2pbmh (ap_pbmh2d P) = P \<and> ap_pbmh2d (ap_d2pbmh Q) = Q"
  sorry

section \<open>Reactive Angelic Designs\<close>

record 'e ap_rp_state =
  ap_tr :: "'e list"
  ap_ref :: "'e set"
  ap_wait :: bool

type_synonym 'e ap_rad_alpha = "'e ap_rp_state ap_ades_alpha"
type_synonym 'e ap_rad_pred = "'e ap_rad_alpha \<Rightarrow> bool"

definition ap_trace_extends :: "'e list \<Rightarrow> 'e list \<Rightarrow> bool" (infix "\<preceq>\<^sub>t" 50) where
  "xs \<preceq>\<^sub>t ys \<longleftrightarrow> (\<exists>zs. ys = xs @ zs)"

definition ap_States_tr_le :: "'e ap_rp_state \<Rightarrow> 'e ap_rp_state set" where
  "ap_States_tr_le s = {z. ap_tr s \<preceq>\<^sub>t ap_tr z}"

definition ap_RA1 :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" where
  "ap_RA1 P = (\<lambda>st.
    let A = ap_ac' st \<inter> ap_States_tr_le (ap_s st)
    in P (st\<lparr>ap_ac' := A\<rparr>) \<and> A \<noteq> {})"

definition ap_drop_trace_prefix :: "'e list \<Rightarrow> 'e list \<Rightarrow> 'e list" where
  "ap_drop_trace_prefix xs ys = drop (length xs) ys"

definition ap_RA2 :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" where
  "ap_RA2 P = (\<lambda>st.
    let s0 = ap_s st;
        sN = s0\<lparr>ap_tr := []\<rparr>;
        acN = {z\<lparr>ap_tr := ap_drop_trace_prefix (ap_tr s0) (ap_tr z)\<rparr> |
          z. z \<in> ap_ac' st \<and> ap_tr s0 \<preceq>\<^sub>t ap_tr z}
    in P (st\<lparr>ap_s := sN, ap_ac' := acN\<rparr>))"

definition ap_IIRAD :: "'e ap_rad_pred" where
  "ap_IIRAD = (\<lambda>st. ap_RA1 (\<lambda>st'. \<not> ap_ok st') st \<or> (ap_ok' st \<and> ap_s st \<in> ap_ac' st))"

definition ap_RA3 :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" where
  "ap_RA3 P = (\<lambda>st. if ap_wait (ap_s st) then ap_IIRAD st else P st)"

definition ap_RA :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" where
  "ap_RA P = ap_RA1 (ap_RA2 (ap_RA3 P))"

definition ap_CSPA1 :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" where
  "ap_CSPA1 P = (\<lambda>st. P st \<or> ap_RA1 (\<lambda>st'. \<not> ap_ok st') st)"

definition ap_CSPA2 :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" where
  "ap_CSPA2 P = ap_H2 P"

definition ap_RAD :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" where
  "ap_RAD P = ap_RA (ap_CSPA1 (ap_CSPA2 (ap_PBMH P)))"

definition ap_el_ac :: "('e ap_rp_state \<Rightarrow> bool) \<Rightarrow> 'e ap_rad_pred" where
  "ap_el_ac R = (\<lambda>st. \<exists>y \<in> ap_ac' st. R y)"

definition ap_RAD_angelic :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" (infixl "\<squnion>\<^sub>R\<^sub>A\<^sub>D" 65) where
  "P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q = (\<lambda>st. P st \<and> Q st)"

definition ap_RAD_demonic :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" (infixl "\<sqinter>\<^sub>R\<^sub>A\<^sub>D" 60) where
  "P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q = (\<lambda>st. P st \<or> Q st)"

definition ap_ChaosRAD :: "'e ap_rad_pred" where
  "ap_ChaosRAD = ap_RA (ap_A ((\<lambda>_. False) \<turnstile>\<^sub>A (\<lambda>st. ap_ac' st \<noteq> {})))"

definition ap_ChoiceRAD :: "'e ap_rad_pred" where
  "ap_ChoiceRAD = ap_RA (ap_A ((\<lambda>_. True) \<turnstile>\<^sub>A (\<lambda>st. ap_ac' st \<noteq> {})))"

definition ap_StopRAD :: "'e ap_rad_pred" where
  "ap_StopRAD = ap_RA (ap_A ((\<lambda>_. True) \<turnstile>\<^sub>A
    (\<lambda>st. \<exists>y \<in> ap_ac' st. ap_tr y = ap_tr (ap_s st) \<and> ap_wait y)))"

definition ap_SkipRAD :: "'e ap_rad_pred" where
  "ap_SkipRAD = ap_RA (ap_A ((\<lambda>_. True) \<turnstile>\<^sub>A
    (\<lambda>st. \<exists>y \<in> ap_ac' st. ap_tr y = ap_tr (ap_s st) \<and> \<not> ap_wait y)))"

definition ap_prefix_RAD :: "'e \<Rightarrow> 'e ap_rad_pred" where
  "ap_prefix_RAD a = ap_RA (ap_A (ap_design (\<lambda>_. True)
    (\<lambda>st. \<exists>y \<in> ap_ac' st.
      (if ap_wait y
       then ap_tr y = ap_tr (ap_s st) \<and> a \<notin> ap_ref y
       else ap_tr y = ap_tr (ap_s st) @ [a]))))"

definition ap_NDRAD :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" where
  "ap_NDRAD P = ap_ChoiceRAD \<squnion>\<^sub>R\<^sub>A\<^sub>D P"

definition ap_p2ac_RAD :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" where
  "ap_p2ac_RAD P = ap_RAD (ap_d2ac P)"

definition ap_ac2p_RAD :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" where
  "ap_ac2p_RAD P = ap_ac2p P"

lemma ap_RA1_idem: "ap_RA1 (ap_RA1 P) = ap_RA1 P"
  sorry

lemma ap_RA2_idem: "ap_RA2 (ap_RA2 P) = ap_RA2 P"
  sorry

lemma ap_RA3_idem: "ap_RA3 (ap_RA3 P) = ap_RA3 P"
  sorry

lemma ap_RA_idem: "ap_RA (ap_RA P) = ap_RA P"
  sorry

lemma ap_RAD_idem: "ap_RAD (ap_RAD P) = ap_RAD P"
  sorry

lemma ap_RA1_A0_absorb: "ap_RA1 (ap_A0 P) = ap_RA1 P"
  sorry

lemma ap_RA2_RA3_commute: "ap_RA2 (ap_RA3 P) = ap_RA3 (ap_RA2 P)"
  sorry

lemma ap_RA1_PBMH_commute: "ap_RA1 (ap_PBMH P) = ap_PBMH (ap_RA1 P)"
  sorry

lemma ap_RA2_PBMH_commute: "ap_RA2 (ap_PBMH P) = ap_PBMH (ap_RA2 P)"
  sorry

lemma ap_RAD_design_form:
  "ap_RAD P = ap_RA (ap_A ((\<lambda>st. \<not> P (st\<lparr>ap_ok' := False\<rparr>)) \<turnstile>\<^sub>A
    (\<lambda>st. P (st\<lparr>ap_ok' := True\<rparr>))))"
  sorry

lemma ap_RAD_angelic_closed:
  assumes "ap_RAD P = P" "ap_RAD Q = Q"
  shows "ap_RAD (P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q) = P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q"
  sorry

lemma ap_RAD_demonic_closed:
  assumes "ap_RAD P = P" "ap_RAD Q = Q"
  shows "ap_RAD (P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q) = P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q"
  sorry

lemma ap_ChaosRAD_angelic_unit:
  assumes "ap_RAD P = P"
  shows "ap_ChaosRAD \<squnion>\<^sub>R\<^sub>A\<^sub>D P = P"
  sorry

lemma ap_ChoiceRAD_is_NDRAD_unit:
  "ap_NDRAD P = ap_ChoiceRAD \<squnion>\<^sub>R\<^sub>A\<^sub>D P"
  sorry

lemma ap_NDRAD_angelic_closed:
  assumes "ap_NDRAD P = P" "ap_NDRAD Q = Q"
  shows "ap_NDRAD (P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q) = P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q"
  sorry

lemma ap_NDRAD_demonic_closed:
  assumes "ap_NDRAD P = P" "ap_NDRAD Q = Q"
  shows "ap_NDRAD (P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q) = P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q"
  sorry

theorem ap_rad_csp_galois:
  "(ap_p2ac_RAD P \<le> Q) \<longleftrightarrow> (P \<le> ap_ac2p_RAD Q)"
  sorry

theorem ap_RAD_CSP_iso_on_A2_NDRAD:
  assumes "ap_A2 P = P" "ap_NDRAD P = P"
  shows "ap_p2ac_RAD (ap_ac2p_RAD P) = P"
  sorry

section \<open>Angelic Processes\<close>

definition ap_IIAP :: "'e ap_rad_pred" where
  "ap_IIAP = ap_H1 (\<lambda>st. ap_ok' st \<and> ap_s st \<in> ap_ac' st)"

definition ap_RA3AP :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" where
  "ap_RA3AP P = (\<lambda>st. if ap_wait (ap_s st) then ap_IIAP st else P st)"

definition ap_AP :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" where
  "ap_AP P = ap_RA3AP (ap_RA2 (ap_A (ap_H1 (ap_CSPA2 P))))"

definition ap_AP_angelic :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" (infixl "\<squnion>\<^sub>A\<^sub>P" 65) where
  "P \<squnion>\<^sub>A\<^sub>P Q = (\<lambda>st. P st \<and> Q st)"

definition ap_AP_demonic :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" (infixl "\<sqinter>\<^sub>A\<^sub>P" 60) where
  "P \<sqinter>\<^sub>A\<^sub>P Q = (\<lambda>st. P st \<or> Q st)"

definition ap_ChaosAP :: "'e ap_rad_pred" where
  "ap_ChaosAP = ap_AP ((\<lambda>_. False) \<turnstile>\<^sub>A (\<lambda>_. True))"

definition ap_ChaosCSPAP :: "'e ap_rad_pred" where
  "ap_ChaosCSPAP = ap_AP ((\<lambda>st. \<not> ap_RA1 (\<lambda>_. True) st) \<turnstile>\<^sub>A (\<lambda>_. True))"

definition ap_ChoiceAP :: "'e ap_rad_pred" where
  "ap_ChoiceAP = ap_AP ((\<lambda>_. True) \<turnstile>\<^sub>A (\<lambda>st. ap_ac' st \<noteq> {}))"

definition ap_NDAP :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" where
  "ap_NDAP P = ap_ChoiceAP \<squnion>\<^sub>A\<^sub>P P"

definition ap_StopAP :: "'e ap_rad_pred" where
  "ap_StopAP = ap_AP ((\<lambda>_. True) \<turnstile>\<^sub>A
    (\<lambda>st. \<exists>y \<in> ap_ac' st. ap_tr y = ap_tr (ap_s st) \<and> ap_wait y))"

definition ap_SkipAP :: "'e ap_rad_pred" where
  "ap_SkipAP = ap_AP ((\<lambda>_. True) \<turnstile>\<^sub>A
    (\<lambda>st. \<exists>y \<in> ap_ac' st. ap_tr y = ap_tr (ap_s st) \<and> \<not> ap_wait y))"

definition ap_prefix_AP :: "'e \<Rightarrow> 'e ap_rad_pred" where
  "ap_prefix_AP a = ap_AP (ap_design (\<lambda>_. True)
    (\<lambda>st. \<exists>y \<in> ap_ac' st.
      (if ap_wait y
       then ap_tr y = ap_tr (ap_s st) \<and> a \<notin> ap_ref y
       else ap_tr y = ap_tr (ap_s st) @ [a])))"

definition ap_rad2ap :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" where
  "ap_rad2ap P = ap_H1 P"

definition ap_ap2rad :: "'e ap_rad_pred \<Rightarrow> 'e ap_rad_pred" where
  "ap_ap2rad P = ap_RA1 P"

lemma ap_RA2_IIAP: "ap_RA2 ap_IIAP = ap_IIAP"
  sorry

lemma ap_RA1_IIAP: "ap_RA1 ap_IIAP = ap_IIRAD"
  sorry

lemma ap_RA3AP_idem: "ap_RA3AP (ap_RA3AP P) = ap_RA3AP P"
  sorry

lemma ap_RA3AP_conj:
  "ap_RA3AP (\<lambda>st. P st \<and> Q st) =
    (\<lambda>st. ap_RA3AP P st \<and> ap_RA3AP Q st)"
  sorry

lemma ap_RA3AP_disj:
  "ap_RA3AP (\<lambda>st. P st \<or> Q st) =
    (\<lambda>st. ap_RA3AP P st \<or> ap_RA3AP Q st)"
  sorry

lemma ap_RA3AP_PBMH_commute:
  "ap_RA3AP (ap_PBMH P) = ap_PBMH (ap_RA3AP P)"
  sorry

lemma ap_RA2_RA3AP_commute:
  "ap_RA2 (ap_RA3AP P) = ap_RA3AP (ap_RA2 P)"
  sorry

lemma ap_RA1_RA3AP_link:
  "ap_RA1 (ap_RA3AP P) = ap_RA3 (ap_RA1 P)"
  sorry

theorem ap_AP_design_form:
  "ap_AP P = ap_RA3AP (ap_RA2 (ap_A
    ((\<lambda>st. \<not> P (st\<lparr>ap_ok' := False\<rparr>)) \<turnstile>\<^sub>A
      (\<lambda>st. P (st\<lparr>ap_ok' := True\<rparr>)))))"
  sorry

lemma ap_AP_idem: "ap_AP (ap_AP P) = ap_AP P"
  sorry

lemma ap_AP_PBMH_healthy: "ap_PBMH (ap_AP P) = ap_AP P"
  sorry

lemma ap_AP_expanded_design:
  "ap_AP P =
    ((\<lambda>st. if ap_wait (ap_s st) then True
      else \<not> ap_RA2 (ap_PBMH (\<lambda>st'. P (st'\<lparr>ap_ok' := False\<rparr>))) st)
     \<turnstile>\<^sub>A
     (\<lambda>st. if ap_wait (ap_s st) then ap_s st \<in> ap_ac' st
      else ap_RA2 (ap_RA1 (ap_PBMH (\<lambda>st'. P (st'\<lparr>ap_ok' := True\<rparr>)))) st))"
  sorry

lemma ap_NDAP_normal_form:
  assumes "ap_AP P = P"
  shows "ap_NDAP P =
    ((\<lambda>_. True) \<turnstile>\<^sub>A
      (\<lambda>st. if ap_wait (ap_s st) then ap_s st \<in> ap_ac' st
        else ap_RA2 (ap_RA1 (ap_PBMH (\<lambda>st'. P (st'\<lparr>ap_ok' := True\<rparr>)))) st))"
  sorry

lemma ap_AP_angelic_closed:
  assumes "ap_AP P = P" "ap_AP Q = Q"
  shows "ap_AP (P \<squnion>\<^sub>A\<^sub>P Q) = P \<squnion>\<^sub>A\<^sub>P Q"
  sorry

lemma ap_AP_demonic_closed:
  assumes "ap_AP P = P" "ap_AP Q = Q"
  shows "ap_AP (P \<sqinter>\<^sub>A\<^sub>P Q) = P \<sqinter>\<^sub>A\<^sub>P Q"
  sorry

lemma ap_NDAP_angelic_closed:
  assumes "ap_NDAP P = P" "ap_NDAP Q = Q"
  shows "ap_NDAP (P \<squnion>\<^sub>A\<^sub>P Q) = P \<squnion>\<^sub>A\<^sub>P Q"
  sorry

lemma ap_NDAP_demonic_closed:
  assumes "ap_NDAP P = P" "ap_NDAP Q = Q"
  shows "ap_NDAP (P \<sqinter>\<^sub>A\<^sub>P Q) = P \<sqinter>\<^sub>A\<^sub>P Q"
  sorry

lemma ap_ChaosAP_explicit:
  "ap_ChaosAP =
    ((\<lambda>st. ap_wait (ap_s st)) \<turnstile>\<^sub>A (\<lambda>st. ap_s st \<in> ap_ac' st))"
  sorry

lemma ap_ChaosCSPAP_explicit:
  "ap_ChaosCSPAP =
    ((\<lambda>st. ap_wait (ap_s st) \<or> \<not> ap_RA1 (\<lambda>_. True) st) \<turnstile>\<^sub>A
      (\<lambda>st. ap_wait (ap_s st) \<and> ap_s st \<in> ap_ac' st))"
  sorry

lemma ap_ChoiceAP_explicit:
  "ap_ChoiceAP =
    ((\<lambda>_. True) \<turnstile>\<^sub>A
      (\<lambda>st. if ap_wait (ap_s st) then ap_s st \<in> ap_ac' st else ap_RA1 (\<lambda>_. True) st))"
  sorry

theorem ap_ChaosAP_angelic_unit:
  assumes "ap_AP P = P"
  shows "P \<squnion>\<^sub>A\<^sub>P ap_ChaosAP = P"
  sorry

theorem ap_H1_ChaosRAD:
  "ap_H1 ap_ChaosRAD = ap_ChaosCSPAP"
  sorry

theorem ap_RA1_ChaosCSPAP:
  "ap_RA1 ap_ChaosCSPAP = ap_ChaosRAD"
  sorry

theorem ap_H1_ChoiceRAD:
  "ap_H1 ap_ChoiceRAD = ap_ChoiceAP"
  sorry

theorem ap_RA1_ChoiceAP:
  "ap_RA1 ap_ChoiceAP = ap_ChoiceRAD"
  sorry

theorem ap_H1_StopRAD:
  "ap_H1 ap_StopRAD = ap_StopAP"
  sorry

theorem ap_RA1_StopAP:
  "ap_RA1 ap_StopAP = ap_StopRAD"
  sorry

theorem ap_H1_SkipRAD:
  "ap_H1 ap_SkipRAD = ap_SkipAP"
  sorry

theorem ap_RA1_SkipAP:
  "ap_RA1 ap_SkipAP = ap_SkipRAD"
  sorry

theorem ap_H1_prefix_RAD:
  "ap_H1 (ap_prefix_RAD a) = ap_prefix_AP a"
  sorry

theorem ap_RA1_prefix_AP:
  "ap_RA1 (ap_prefix_AP a) = ap_prefix_RAD a"
  sorry

theorem ap_rad_ap_galois:
  "(ap_rad2ap P \<le> Q) \<longleftrightarrow> (P \<le> ap_ap2rad Q)"
  sorry

theorem ap_NDAP_RAD_iso:
  assumes "ap_NDAP P = P"
  shows "ap_rad2ap (ap_ap2rad P) = P"
  sorry

lemma ap_AP_seq_closed:
  assumes "ap_AP P = P" "ap_AP Q = Q"
  shows "ap_AP (P ;\<^sub>D\<^sub>a\<^sub>c Q) = P ;\<^sub>D\<^sub>a\<^sub>c Q"
  sorry

lemma ap_NDAP_seq_closed:
  assumes "ap_NDAP P = P" "ap_NDAP Q = Q"
  shows "ap_NDAP (P ;\<^sub>D\<^sub>a\<^sub>c Q) = P ;\<^sub>D\<^sub>a\<^sub>c Q"
  sorry

lemma ap_prefix_ChaosAP:
  "ap_prefix_AP a ;\<^sub>D\<^sub>a\<^sub>c ap_ChaosAP = ap_ChaosAP"
  sorry

lemma ap_prefix_ChaosCSPAP:
  "ap_prefix_AP a ;\<^sub>D\<^sub>a\<^sub>c ap_ChaosCSPAP =
    ap_AP ((\<lambda>st. \<not> (\<exists>y \<in> ap_ac' st. ap_tr (ap_s st) @ [a] \<preceq>\<^sub>t ap_tr y)) \<turnstile>\<^sub>A
      (\<lambda>st. \<exists>y \<in> ap_ac' st. ap_wait y \<and> ap_tr y = ap_tr (ap_s st) \<and> a \<notin> ap_ref y))"
  sorry

theorem ap_angelic_avoids_divergence:
  "ap_prefix_AP a ;\<^sub>D\<^sub>a\<^sub>c ap_ChaosAP \<squnion>\<^sub>A\<^sub>P ap_prefix_AP b = ap_prefix_AP b"
  sorry

theorem ap_headline_theorem:
  "ap_prefix_AP a \<squnion>\<^sub>A\<^sub>P (ap_prefix_AP b ;\<^sub>D\<^sub>a\<^sub>c ap_ChaosAP) = ap_prefix_AP a"
  sorry

section \<open>Roadmap Notes\<close>

text \<open>
  Next proof batches, in dependency order:

  \<^enum> Close the BMH fixed-point lemmas and the bmh012/bmh0132
  characterisations.  These are set-theoretic and should be good Sledgehammer
  warm-up targets.

  \<^enum> Replace the shallow design records with established UTP alphabet syntax where
  this improves reuse, while preserving the names in this file as compatibility
  wrappers.

  \<^enum> Prove A0/A1/A2 laws, then the d2bmb/bmb2d and d2ac/ac2p linking
  theorems.

  \<^enum> Prove RA1/RA2/RA3 commutation and closure lemmas before attempting RAD to
  CSP linking.

  \<^enum> Prove the RA3AP commutation lemmas, AP normal forms, and the RAD/AP Galois
  connection.

  \<^enum> Finish with the prefix/divergence lemmas and the headline theorem.
\<close>

end
