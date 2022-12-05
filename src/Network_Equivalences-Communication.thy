section \<open>Constructs for Describing Communication\<close>

theory "Network_Equivalences-Communication"
  imports "Thorn_Calculus.Thorn_Calculus-Core_Bisimilarities"
begin

subsection \<open>Distributors\<close>

definition distributor :: "chan family \<Rightarrow> chan family list \<Rightarrow> process family" (infix \<open>\<Rightarrow>\<close> 52) where
  [simp]: "A \<Rightarrow> Bs = A \<triangleright>\<^sup>\<infinity> x. \<Prod>B \<leftarrow> Bs. B \<triangleleft> \<box> x"

lemma adapted_after_distributor:
  shows "(A \<Rightarrow> Bs) \<guillemotleft> \<E> = A \<guillemotleft> \<E> \<Rightarrow> map (\<lambda>B. B \<guillemotleft> \<E>) Bs"
  sorry

lemma transition_from_distributor:
  assumes "A \<Rightarrow> Bs \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> Q"
  obtains n and X
    where
      "\<alpha> = A \<triangleright> \<star>\<^bsup>n\<^esup> X"
    and
      "Q = \<Prod>B \<leftarrow> Bs. B \<guillemotleft> suffix n \<triangleleft> X \<parallel> (A \<Rightarrow> Bs) \<guillemotleft> suffix n"
proof -
  obtain n and X
    where "\<alpha> = A \<triangleright> \<star>\<^bsup>n\<^esup> X" and "Q = post_receive n X (\<lambda>x. \<Prod>B \<leftarrow> Bs. B \<triangleleft> \<box> x) \<parallel> (A \<Rightarrow> Bs) \<guillemotleft> suffix n"
    unfolding distributor_def
    using assms
    by (fastforce elim: transition_from_repeated_receive)
  moreover have "post_receive n X (\<lambda>x. B \<triangleleft> \<box> x) = B \<guillemotleft> suffix n \<triangleleft> X" for B
    unfolding post_receive_after_send and post_receive_def
    by (transfer, simp)
  then have "post_receive n X (\<lambda>x. \<Prod>B \<leftarrow> Bs. B \<triangleleft> \<box> x) = \<Prod>B \<leftarrow> Bs. B \<guillemotleft> suffix n \<triangleleft> X"
    by
      (
        induction Bs,
        unfold general_parallel.simps post_receive_after_parallel post_receive_after_stop
      ) simp_all
  ultimately show ?thesis
    by (simp only: that)
qed

lemma distributor_idempotency [thorn_simps]:
  shows "A \<Rightarrow> Bs \<parallel> A \<Rightarrow> Bs \<sim>\<^sub>s A \<Rightarrow> Bs"
  unfolding distributor_def
  using repeated_receive_idempotency .

lemma distributor_nested_idempotency [thorn_simps]:
  shows "A \<Rightarrow> Bs \<parallel> (A \<Rightarrow> Bs \<parallel> P) \<sim>\<^sub>s A \<Rightarrow> Bs \<parallel> P"
  unfolding distributor_def
  using repeated_receive_nested_idempotency .

(*FIXME: Check whether we should add this lemma to \<^theory_text>\<open>thorn_simps\<close>. *)
lemma inner_distributor_redundancy:
  shows "A \<Rightarrow> Bs \<parallel> C \<triangleright>\<^sup>\<infinity> x. (A \<Rightarrow> Bs \<parallel> \<P> x) \<sim>\<^sub>s A \<Rightarrow> Bs \<parallel> C \<triangleright>\<^sup>\<infinity> x. \<P> x"
  unfolding distributor_def
  using inner_repeated_receive_redundancy .

subsection \<open>Loss Servers\<close>

definition loss :: "chan family \<Rightarrow> process family" (\<open>\<currency>\<^sup>?\<close>) where
  [simp]: "\<currency>\<^sup>? A = A \<Rightarrow> []"

lemma adapted_after_loss:
  shows "\<currency>\<^sup>? A \<guillemotleft> \<E> = \<currency>\<^sup>? (A \<guillemotleft> \<E>)"
  by (simp del: distributor_def add: adapted_after_distributor)

lemma loss_idempotency [thorn_simps]:
  shows "\<currency>\<^sup>? A \<parallel> \<currency>\<^sup>? A \<sim>\<^sub>s \<currency>\<^sup>? A"
  unfolding loss_def
  using distributor_idempotency .

lemma loss_nested_idempotency [thorn_simps]:
  shows "\<currency>\<^sup>? A \<parallel> (\<currency>\<^sup>? A \<parallel> P) \<sim>\<^sub>s \<currency>\<^sup>? A \<parallel> P"
  unfolding loss_def
  using distributor_nested_idempotency .

lemma inner_loss_redundancy:
  shows "\<currency>\<^sup>? A \<parallel> B \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>? A \<parallel> \<P> x) \<sim>\<^sub>s \<currency>\<^sup>? A \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x"
  unfolding loss_def
  using inner_distributor_redundancy .

subsection \<open>Duplication Servers\<close>

definition duplication :: "chan family \<Rightarrow> process family" (\<open>\<currency>\<^sup>+\<close>) where
  [simp]: "\<currency>\<^sup>+ A = A \<Rightarrow> [A, A]"

lemma adapted_after_duplication:
  shows "\<currency>\<^sup>+ A \<guillemotleft> \<E> = \<currency>\<^sup>+ (A \<guillemotleft> \<E>)"
  by (simp del: distributor_def add: adapted_after_distributor)

lemma transition_from_duplication:
  assumes "\<currency>\<^sup>+ A \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> Q"
  obtains n and X
    where
      "\<alpha> = A \<triangleright> \<star>\<^bsup>n\<^esup> X"
    and
      "Q = (A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n"
  using assms unfolding duplication_def
  by (fastforce elim: transition_from_distributor)

lemma duplication_idempotency [thorn_simps]:
  shows "\<currency>\<^sup>+ A \<parallel> \<currency>\<^sup>+ A \<sim>\<^sub>s \<currency>\<^sup>+ A"
  unfolding duplication_def
  using distributor_idempotency .

lemma duplication_nested_idempotency [thorn_simps]:
  shows "\<currency>\<^sup>+ A \<parallel> (\<currency>\<^sup>+ A \<parallel> P) \<sim>\<^sub>s \<currency>\<^sup>+ A \<parallel> P"
  unfolding duplication_def
  using distributor_nested_idempotency .

lemma inner_duplication_redundancy:
  shows "\<currency>\<^sup>+ A \<parallel> B \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>+ A \<parallel> \<P> x) \<sim>\<^sub>s \<currency>\<^sup>+ A \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x"
  unfolding duplication_def
  using inner_distributor_redundancy .

context begin

private lemma double_send_unsplit_repeated_receive_rearrangement:
  shows "
    ((A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n
    \<sim>\<^sub>s
    (A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> (\<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
  unfolding adapted_after_parallel
  using parallel_associativity .

private lemma double_send_split_repeated_receive_rearrangement:
  shows "
    (A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> (\<currency>\<^sup>+ A \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x)) \<guillemotleft> suffix n
    \<sim>\<^sub>s
    ((A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
    (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x) \<guillemotleft> suffix n"
  unfolding adapted_after_parallel
  using parallel_associativity [symmetric] .

lemma repeated_receive_split:
  assumes
    "P' \<sim>\<^sub>s \<zero>" and "Q' \<sim>\<^sub>s \<zero>"
  and
    "\<And>n X. post_receive n X \<P> \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> P'" and "\<And>n X. post_receive n X \<Q> \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q'"
  shows "\<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x) \<approx>\<^sub>s \<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x"
unfolding synchronous.weak_bisimilarity_is_mixed_bisimilarity
proof (coinduction rule: synchronous.mixed.up_to_rule [where \<F> = "[\<sim>\<^sub>s] \<frown> \<M> \<frown> [\<sim>\<^sub>s]"])
  case (forward_simulation \<alpha> S)
  then show ?case
  proof cases
    case (parallel_left_io \<eta> A' n X Q)
    from \<open>\<currency>\<^sup>+ A \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> Q\<close>
    have
      "\<eta> = Receiving"
    and
      "A' = A"
    and
      "Q = (A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n"
      by (blast elim: transition_from_duplication)+
    with \<open>\<currency>\<^sup>+ A \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> Q\<close>
    have "\<currency>\<^sup>+ A \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> (A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n"
      by (simp only:)
    then have "
      \<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x
      \<Rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
      ((A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
      (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x) \<guillemotleft> suffix n"
      by
        (intro
          synchronous_transition.parallel_left_io
          synchronous.transition_in_weak_transition_rule
        )
    then show ?thesis
      unfolding
        \<open>\<alpha> = IO \<eta> A' n X\<close> and \<open>S = Q \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n\<close>
      and
        \<open>\<eta> = Receiving\<close>
      and
        \<open>A' = A\<close>
      and
        \<open>Q = (A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n\<close>
      using
        double_send_unsplit_repeated_receive_rearrangement
      and
        double_send_split_repeated_receive_rearrangement
      and
        composition_in_universe
          [OF suffix_adapted_mutation_in_universe parallel_mutation_in_universe]
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  next
    case (parallel_right_io \<eta> A' n X Q)
    from \<open>A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x) \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> Q\<close>
    have
      "\<eta> = Receiving"
    and
      "A' = A"
    and
      "Q = post_receive n X (\<lambda>x. \<P> x \<parallel> \<Q> x) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
      by (auto elim: transition_from_repeated_receive)
    with \<open>A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x) \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> Q\<close>
    have "
      A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)
      \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
      post_receive n X (\<lambda>x. \<P> x \<parallel> \<Q> x) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
      by (simp only:)
    then have "
      \<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)
      \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
      \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> post_receive n X (\<lambda>x. \<P> x \<parallel> \<Q> x) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
      by (fact synchronous_transition.parallel_right_io)
    moreover
    have "
      \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (post_receive n X \<P> \<parallel> post_receive n X \<Q>) \<parallel>
      post_receive n X (\<lambda>x. A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x))
      \<sim>\<^sub>s
      (post_receive n X \<P> \<parallel> post_receive n X \<Q>) \<parallel> (\<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
      unfolding adapted_after_parallel and post_receive_def
      using parallel_left_commutativity .
    moreover
    have "
      \<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x
      \<Rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
      ((\<zero> \<parallel> \<zero> \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
      ((post_receive n X \<P> \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n) \<parallel>
       (post_receive n X \<Q> \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n))"
    proof -
      have "
        \<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x
        \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
        (((A \<guillemotleft> suffix n) \<triangleleft> X \<parallel> (A \<guillemotleft> suffix n) \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
        (A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n)"
      proof -
        have "\<currency>\<^sup>+ A \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> post_receive n X (\<lambda>x. \<Prod>B \<leftarrow> [A, A]. B \<triangleleft> \<box> x \<parallel> \<currency>\<^sup>+ A)"
          unfolding distributor_def and duplication_def
          using receiving
          by (subst repeated_receive_proper_def)
        then have "
          \<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x
          \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
          post_receive n X (\<lambda>x. \<Prod>B \<leftarrow> [A, A]. B \<triangleleft> \<box> x \<parallel> \<currency>\<^sup>+ A) \<parallel>
          (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x) \<guillemotleft> suffix n"
          by (fact parallel_left_io)
        then have "
          \<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x
          \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
          post_receive n X (\<lambda>x. \<Prod>B \<leftarrow> [A, A]. B \<triangleleft> \<box> x \<parallel> \<currency>\<^sup>+ A) \<parallel>
          (A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n)"
          unfolding adapted_after_parallel and adapted_after_repeated_receive .
        moreover
        have "
          post_receive n X (\<lambda>x. \<Prod>B \<leftarrow> [A, A]. B \<triangleleft> \<box> x \<parallel> \<currency>\<^sup>+ A)
          =
          (A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n"
        proof -
          have "
            post_receive n X (\<lambda>x. \<Prod>B \<leftarrow> [A, A]. B \<triangleleft> \<box> x \<parallel> \<currency>\<^sup>+ A)
            =
            post_receive n X (\<lambda>x. \<Prod>B \<leftarrow> [A, A]. B \<triangleleft> \<box> x) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n"
            unfolding post_receive_after_parallel and post_receive_def ..
          also have "\<dots> = post_receive n X (\<lambda>x. A \<triangleleft> \<box> x \<parallel> A \<triangleleft> \<box> x \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n"
            unfolding general_parallel.simps ..
          also have "\<dots> = (post_receive n X (\<lambda>x. A \<triangleleft> \<box> x) \<parallel> post_receive n X (\<lambda>x. A \<triangleleft> \<box> x) \<parallel> \<zero>) \<parallel>
            \<currency>\<^sup>+ A \<guillemotleft> suffix n"
            unfolding post_receive_after_parallel and post_receive_after_stop ..
          also have "\<dots> =
            (post_receive n X (\<lambda>_. A) \<triangleleft> X \<parallel> post_receive n X (\<lambda>_. A) \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n"
            unfolding post_receive_after_send and post_receive_def
            by (transfer, simp)
          also have "\<dots> = (A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n"
            unfolding post_receive_def ..
          finally show ?thesis .
        qed
        ultimately show ?thesis
          by (simp only:)
      qed
      moreover
      have "
        ((A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
        (A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n)
        \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr>
        ((\<zero> \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
        ((post_receive n X \<P> \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n) \<parallel>
         A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n)"
      proof -
        have "A \<guillemotleft> suffix n \<triangleleft> X \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> suffix n \<triangleleft> \<star>\<^bsup>0\<^esup> X\<rparr> \<zero>"
          by (fact sending)
        then have "
          A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero> \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> suffix n \<triangleleft> \<star>\<^bsup>0\<^esup> X\<rparr> \<zero> \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>"
          unfolding post_receive_def
          using parallel_left_io [where n = 0]
          by (transfer, simp)
        then have "
          (A \<guillemotleft> suffix n \<triangleleft> X \<parallel> (A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>)) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n
          \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> suffix n \<triangleleft> \<star>\<^bsup>0\<^esup> X\<rparr>
          (\<zero> \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n"
          using parallel_left_io [where n = 0]
          by (transfer, simp)
        moreover
        have "
          A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n
          \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> suffix n \<triangleright> \<star>\<^bsup>0\<^esup> X\<rparr>
          post_receive 0 X (\<lambda>x. \<P> x \<guillemotleft> suffix n \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n)"
          using receiving
          by (subst repeated_receive_proper_def)
        then have "
          A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n
          \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> suffix n \<triangleright> \<star>\<^bsup>0\<^esup> X\<rparr>
          (post_receive 0 X (\<lambda>x. \<P> x \<guillemotleft> suffix n \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n)) \<parallel>
          A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n"
          using parallel_left_io [where n = 0]
          by (transfer, simp)
        ultimately have "
          ((A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
          (A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n)
          \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr>
          ((\<zero> \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
          ((post_receive 0 X (\<lambda>x. \<P> x \<guillemotleft> suffix n \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n)) \<parallel>
           A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n)"
          using communication [where n = 0]
          by fastforce
        then have "
          ((A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
          (A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n)
          \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr>
          ((\<zero> \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
          ((post_receive n X \<P> \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n) \<parallel>
           A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n)"
          unfolding post_receive_def
          by (transfer, simp)
        then show ?thesis .
      qed
      moreover
      have "
        ((\<zero> \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
        ((post_receive n X \<P> \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n) \<parallel>
         A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n)
        \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr>
        ((\<zero> \<parallel> \<zero> \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
        ((post_receive n X \<P> \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n) \<parallel>
         (post_receive n X \<Q> \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n))"
      proof -
        have "A \<guillemotleft> suffix n \<triangleleft> X \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> suffix n \<triangleleft> \<star>\<^bsup>0\<^esup> X\<rparr> \<zero>"
          by (fact sending)
        then have "
          A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero> \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> suffix n \<triangleleft> \<star>\<^bsup>0\<^esup> X\<rparr> \<zero> \<parallel> \<zero>"
          using parallel_left_io
          by (transfer, simp)
        then have "
          \<zero> \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero> \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> suffix n \<triangleleft> \<star>\<^bsup>0\<^esup> X\<rparr> \<zero> \<parallel> \<zero> \<parallel> \<zero>"
          using synchronous_transition.parallel_right_io
          by (transfer, simp)
        then have "
          (\<zero> \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n
          \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> suffix n \<triangleleft> \<star>\<^bsup>0\<^esup> X\<rparr>
          (\<zero> \<parallel> \<zero> \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n"
          using parallel_left_io [where n = 0]
          by (transfer, simp)
        moreover
        have "
          A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n
          \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> suffix n \<triangleright> \<star>\<^bsup>0\<^esup> X\<rparr>
          post_receive 0 X (\<lambda>x. \<Q> x \<guillemotleft> suffix n \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n)"
          using receiving
          by (subst repeated_receive_proper_def)
        then have "
          (post_receive n X \<P> \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n) \<parallel>
          A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n
          \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> suffix n \<triangleright> \<star>\<^bsup>0\<^esup> X\<rparr>
          (post_receive n X \<P> \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n) \<parallel>
          post_receive 0 X (\<lambda>x. \<Q> x \<guillemotleft> suffix n \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n)"
          using synchronous_transition.parallel_right_io [where n = 0]
          by (transfer, simp)
        ultimately have "
          ((\<zero> \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
          ((post_receive n X \<P> \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n) \<parallel>
           A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n)
          \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr>
          ((\<zero> \<parallel> \<zero> \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
          ((post_receive n X \<P> \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n) \<parallel>
           post_receive 0 X (\<lambda>x. \<Q> x \<guillemotleft> suffix n \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n))"
          using communication
          by fastforce
        then have "
          ((\<zero> \<parallel> (A \<guillemotleft> suffix n) \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
          ((post_receive n X \<P> \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n) \<parallel>
           A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n)
          \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr>
          ((\<zero> \<parallel> \<zero> \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
          ((post_receive n X \<P> \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n) \<parallel>
           (post_receive n X \<Q> \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n))"
          unfolding post_receive_def
          by (transfer, simp)
        then show ?thesis .
      qed
      ultimately show ?thesis
        by (simp, blast intro: rtranclp_trans)
    qed
    moreover
    have "
      (post_receive n X \<P> \<parallel> post_receive n X \<Q>) \<parallel> (\<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x) \<guillemotleft> suffix n
      \<sim>\<^sub>s
      ((\<zero> \<parallel> \<zero> \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
      ((post_receive n X \<P> \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n) \<parallel>
       (post_receive n X \<Q> \<parallel> A \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<Q> x \<guillemotleft> suffix n))"
      unfolding adapted_after_repeated_receive and adapted_after_parallel
      using thorn_simps
      by equivalence
    ultimately show ?thesis
      unfolding
        post_receive_after_parallel
      and
        \<open>\<alpha> = IO \<eta> A' n X\<close> and \<open>S = \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> Q\<close>
      and
        \<open>\<eta> = Receiving\<close>
      and
        \<open>A' = A\<close>
      and
        \<open>Q = post_receive n X (\<lambda>x. \<P> x \<parallel> \<Q> x) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n\<close>
      using
        composition_in_universe
          [OF suffix_adapted_mutation_in_universe parallel_mutation_in_universe]
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  qed (fastforce elim: transition_from_repeated_receive)+
next
  case (backward_simulation \<alpha> S)
  then show ?case
  proof cases
    case (communication \<eta> \<mu> A' n X P Q)
    from \<open>\<currency>\<^sup>+ A \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> P\<close> have "\<eta> = Receiving"
      by (fastforce elim: transition_from_repeated_receive)
    moreover
    from \<open>A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x \<rightarrow>\<^sub>s\<lparr>IO \<mu> A' n X\<rparr> Q\<close> have "\<mu> = Receiving"
      by (cases, auto elim: transition_from_repeated_receive)
    ultimately show ?thesis
      using \<open>\<eta> \<noteq> \<mu>\<close> by blast
  next
    case (parallel_left_communication P)
    then show ?thesis
      by (fastforce elim: transition_from_repeated_receive)
  next
    case (parallel_right_communication Q)
    from \<open>A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q\<close> show ?thesis
      by cases (fastforce elim: transition_from_repeated_receive)+
  next
    case (parallel_left_io \<eta> A' n X Q)
    from \<open>\<currency>\<^sup>+ A \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> Q\<close>
    have
      "\<eta> = Receiving"
    and
      "A' = A"
    and
      "Q = (A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n"
      by (blast elim: transition_from_duplication)+
    with \<open>\<currency>\<^sup>+ A \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> Q\<close>
    have "\<currency>\<^sup>+ A \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> (A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n"
      by (simp only:)
    then have "
      \<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)
      \<Rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
      ((A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel>
      (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
      by
        (intro
          synchronous_transition.parallel_left_io
          synchronous.transition_in_weak_transition_rule
        )
    then show ?thesis
      unfolding
        \<open>\<alpha> = IO \<eta> A' n X\<close> and \<open>S = Q \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x) \<guillemotleft> suffix n\<close>
      and
        \<open>\<eta> = Receiving\<close>
      and
        \<open>A' = A\<close>
      and
        \<open>Q = (A \<guillemotleft> suffix n \<triangleleft> X \<parallel> A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n\<close>
      using
        double_send_unsplit_repeated_receive_rearrangement
      and
        double_send_split_repeated_receive_rearrangement
      and
        composition_in_universe
          [OF suffix_adapted_mutation_in_universe parallel_mutation_in_universe]
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  next
    case (parallel_right_io \<eta> A' n X Q)
    from \<open>A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> Q\<close> show ?thesis
    proof cases
      case (parallel_left_io R)
      from \<open>A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> R\<close>
      have
        "\<eta> = Receiving"
      and
        "A' = A"
      and
        "R = post_receive n X \<P> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
        by (auto elim: transition_from_repeated_receive)
      with \<open>A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> R\<close>
      have "A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> post_receive n X \<P> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
        by (simp only:)
      then have "
        A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x
        \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
        (post_receive n X \<P> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<Q> x) \<guillemotleft> suffix n"
        by (fact synchronous_transition.parallel_left_io)
      then have "
        \<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x
        \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
        \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (post_receive n X \<P> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<Q> x) \<guillemotleft> suffix n"
        by (fact synchronous_transition.parallel_right_io)
      moreover
      have "
        post_receive n X \<P> \<parallel> (\<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x) \<guillemotleft> suffix n
        \<sim>\<^sub>s
        \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (post_receive n X \<P> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<Q> x) \<guillemotleft> suffix n"
        unfolding adapted_after_parallel
        using thorn_simps
        by equivalence
      moreover
      have "
        \<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)
        \<Rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
        \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (post_receive n X \<P> \<parallel> Q') \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
      proof -
        have "
          A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)
          \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
          post_receive n X (\<lambda>x. (\<P> x \<parallel> \<Q> x) \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x))"
          using receiving
          by (subst repeated_receive_proper_def)
        then have "
          \<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)
          \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
          \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> post_receive n X (\<lambda>x. (\<P> x \<parallel> \<Q> x) \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x))"
          by (fact synchronous_transition.parallel_right_io)
        moreover
        have "
          post_receive n X (\<lambda>x. (\<P> x \<parallel> \<Q> x) \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x))
          =
          (post_receive n X \<P> \<parallel> post_receive n X \<Q>) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
          unfolding post_receive_after_parallel and post_receive_def ..
        ultimately have "
          \<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)
          \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
          \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (post_receive n X \<P> \<parallel> post_receive n X \<Q>) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
          by (simp only:)
        moreover
        from \<open>post_receive n X \<Q> \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q'\<close>
        have "
          \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (post_receive n X \<P> \<parallel> post_receive n X \<Q>) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n
          \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr>
          \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (post_receive n X \<P> \<parallel> Q') \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
          by (blast intro: parallel_left_communication parallel_right_communication)
        ultimately show ?thesis
          by (simp, blast intro: rtranclp_trans)
      qed
      moreover
      have "
        \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (post_receive n X \<P> \<parallel> Q') \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n
        \<sim>\<^sub>s
        post_receive n X \<P> \<parallel> (\<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
      proof -
        from \<open>Q' \<sim>\<^sub>s \<zero>\<close> have "
          \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (post_receive n X \<P> \<parallel> Q') \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n
          \<sim>\<^sub>s
          \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> post_receive n X \<P> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
          using parallel_right_identity
          by equivalence
        also have "\<dots> \<sim>\<^sub>s post_receive n X \<P> \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
          by (fact parallel_left_commutativity)
        also have "\<dots> = post_receive n X \<P> \<parallel> (\<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
          unfolding adapted_after_parallel ..
        finally show ?thesis .
      qed
      ultimately show ?thesis
        unfolding
          \<open>\<alpha> = IO \<eta> A' n X\<close> and \<open>S = \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> Q\<close>
        and
          \<open>\<eta> = Receiving\<close> and \<open>A' = A\<close> and \<open>Q = R \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<Q> x) \<guillemotleft> suffix n\<close>
        and
          \<open>R = post_receive n X \<P> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n\<close>
        using
          composition_in_universe
            [OF suffix_adapted_mutation_in_universe parallel_mutation_in_universe]
        by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
    next
      case (parallel_right_io R)
      from \<open>A \<triangleright>\<^sup>\<infinity> x. \<Q> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> R\<close>
      have
        "\<eta> = Receiving"
      and
        "A' = A"
      and
        "R = post_receive n X \<Q> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<Q> x) \<guillemotleft> suffix n"
        by (auto elim: transition_from_repeated_receive)
      with \<open>A \<triangleright>\<^sup>\<infinity> x. \<Q> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> R\<close>
      have "A \<triangleright>\<^sup>\<infinity> x. \<Q> x \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> post_receive n X \<Q> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<Q> x) \<guillemotleft> suffix n"
        by (simp only:)
      then have "
        A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x
        \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
        (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n \<parallel> post_receive n X \<Q> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<Q> x) \<guillemotleft> suffix n"
        by (fact synchronous_transition.parallel_right_io)
      then have "
        \<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x
        \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
        \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n \<parallel> post_receive n X \<Q> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<Q> x) \<guillemotleft> suffix n"
        by (fact synchronous_transition.parallel_right_io)
      moreover
      have "
        post_receive n X \<Q> \<parallel> (\<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x) \<guillemotleft> suffix n
        \<sim>\<^sub>s
        \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n \<parallel> post_receive n X \<Q> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<Q> x) \<guillemotleft> suffix n"
        unfolding adapted_after_parallel
        using thorn_simps
        by equivalence
      moreover
      have "
        \<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)
        \<Rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
        \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (P' \<parallel> post_receive n X \<Q>) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
      proof -
        have "
          A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)
          \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
          post_receive n X (\<lambda>x. (\<P> x \<parallel> \<Q> x) \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x))"
          using receiving
          by (subst repeated_receive_proper_def)
        then have "
          \<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)
          \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
          \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> post_receive n X (\<lambda>x. (\<P> x \<parallel> \<Q> x) \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x))"
          by (fact synchronous_transition.parallel_right_io)
        moreover
        have "
          post_receive n X (\<lambda>x. (\<P> x \<parallel> \<Q> x) \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x))
          =
          (post_receive n X \<P> \<parallel> post_receive n X \<Q>) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
          unfolding post_receive_after_parallel and post_receive_def ..
        ultimately have "
          \<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)
          \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
          \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (post_receive n X \<P> \<parallel> post_receive n X \<Q>) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
          by (simp only:)
        moreover
        from \<open>post_receive n X \<P> \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> P'\<close>
        have "
          \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (post_receive n X \<P> \<parallel> post_receive n X \<Q>) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n
          \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr>
          \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (P' \<parallel> post_receive n X \<Q>) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
          by (blast intro: parallel_left_communication parallel_right_communication)
        ultimately show ?thesis
          by (simp, blast intro: rtranclp_trans)
      qed
      moreover
      have "
        \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (P' \<parallel> post_receive n X \<Q>) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n
        \<sim>\<^sub>s
        post_receive n X \<Q> \<parallel> (\<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
      proof -
        from \<open>P' \<sim>\<^sub>s \<zero>\<close> have "
          \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (P' \<parallel> post_receive n X \<Q>) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n
          \<sim>\<^sub>s
          \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> post_receive n X \<Q> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
          using parallel_left_identity
          by equivalence
        also have "\<dots> \<sim>\<^sub>s post_receive n X \<Q> \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
          by (fact parallel_left_commutativity)
        also have "\<dots> = post_receive n X \<Q> \<parallel> (\<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x)) \<guillemotleft> suffix n"
          unfolding adapted_after_parallel ..
        finally show ?thesis .
      qed
      ultimately show ?thesis
        unfolding
          \<open>\<alpha> = IO \<eta> A' n X\<close> and \<open>S = \<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> Q\<close>
        and
          \<open>\<eta> = Receiving\<close> and \<open>A' = A\<close> and \<open>Q = (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n \<parallel> R\<close>
        and
          \<open>R = post_receive n X \<Q> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<Q> x) \<guillemotleft> suffix n\<close>
        using
          composition_in_universe
            [OF suffix_adapted_mutation_in_universe parallel_mutation_in_universe]
        by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
    qed
  qed
qed respectful

end

subsection \<open>Duploss Servers\<close>

definition duploss :: "chan family \<Rightarrow> process family" (\<open>\<currency>\<^sup>*\<close>) where
  [simp]: "\<currency>\<^sup>* A = \<currency>\<^sup>? A \<parallel> \<currency>\<^sup>+ A"

lemma adapted_after_duploss:
  shows "\<currency>\<^sup>* A \<guillemotleft> \<E> = \<currency>\<^sup>* (A \<guillemotleft> \<E>)"
  by (simp only: duploss_def adapted_after_parallel adapted_after_loss adapted_after_duplication)

lemma duploss_idempotency [thorn_simps]:
  shows "\<currency>\<^sup>* A \<parallel> \<currency>\<^sup>* A \<sim>\<^sub>s \<currency>\<^sup>* A"
  unfolding duploss_def
  using thorn_simps
  by equivalence

lemma duploss_nested_idempotency [thorn_simps]:
  shows "\<currency>\<^sup>* A \<parallel> (\<currency>\<^sup>* A \<parallel> P) \<sim>\<^sub>s \<currency>\<^sup>* A \<parallel> P"
  unfolding duploss_def
  using thorn_simps
  by equivalence

(*FIXME:
  Simplify the proof of the following lemma once #231 is resolved.

  In particular, do the following:

    \<^item> Turn the detailed proofs that involve
      \<^theory_text>\<open>repeated_receive_is_quasi_compatible_with_synchronous_bisimilarity\<close> into single-step proofs
      that use the \<^theory_text>\<open>bisimilarity\<close> proof method.

    \<^item> Merge the resulting proofs with adjacent proofs if \<^theory_text>\<open>bisimilarity\<close> can solve the whole step.

    \<^item> Merge applications of \<^theory_text>\<open>parallel_commutativity\<close> and \<^theory_text>\<open>parallel_associativity\<close> when possible.

    \<^item> Get rid of applications of compatibility rules whenever \<^theory_text>\<open>bisimilarity\<close> can be used instead.
*)
lemma inner_duploss_redundancy:
  shows "\<currency>\<^sup>* A \<parallel> B \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>* A \<parallel> \<P> x) \<sim>\<^sub>s \<currency>\<^sup>* A \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x"
proof -
  have "
    post_receive n X (\<lambda>x. (\<currency>\<^sup>? A \<parallel> \<currency>\<^sup>+ A) \<parallel> \<P> x)
    \<sim>\<^sub>s
    post_receive n X (\<lambda>x. \<currency>\<^sup>? A \<parallel> (\<currency>\<^sup>+ A \<parallel> \<P> x))"
    for n and X
  proof -
    have "
      (\<lambda>e. (((\<currency>\<^sup>? A \<parallel> \<currency>\<^sup>+ A) \<parallel> \<P> (X e)) \<guillemotleft> suffix n) e)
      =
      (\<lambda>e. ((\<currency>\<^sup>? A \<guillemotleft> suffix n \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel> \<P> (X e) \<guillemotleft> suffix n) e)"
      by (simp only: adapted_after_parallel)
    also have "\<dots> = (\<currency>\<^sup>? A \<guillemotleft> suffix n \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel> (\<lambda>e. (\<P> (X e) \<guillemotleft> suffix n) e)"
      by (subst environment_dependent_parallel) (fact refl)
    also have "\<dots> \<sim>\<^sub>s \<currency>\<^sup>? A \<guillemotleft> suffix n \<parallel> (\<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (\<lambda>e. (\<P> (X e) \<guillemotleft> suffix n) e))"
      using parallel_associativity .
    also have "\<dots> = (\<lambda>e. (\<currency>\<^sup>? A \<guillemotleft> suffix n \<parallel> (\<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> \<P> (X e) \<guillemotleft> suffix n)) e)"
      by
        (subst (3) environment_dependent_parallel, subst (4) environment_dependent_parallel)
        (fact refl)
    also have "\<dots> = (\<lambda>e. ((\<currency>\<^sup>? A \<parallel> (\<currency>\<^sup>+ A \<parallel> \<P> (X e))) \<guillemotleft> suffix n) e)"
      by (simp only: adapted_after_parallel)
    finally show ?thesis
      unfolding post_receive_def .
  qed
  then have "
    (\<currency>\<^sup>? A \<parallel> \<currency>\<^sup>+ A) \<parallel> B \<triangleright>\<^sup>\<infinity> x. ((\<currency>\<^sup>? A \<parallel> \<currency>\<^sup>+ A) \<parallel> \<P> x)
    \<sim>\<^sub>s
    (\<currency>\<^sup>? A \<parallel> \<currency>\<^sup>+ A) \<parallel> B \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>? A \<parallel> (\<currency>\<^sup>+ A \<parallel> \<P> x))"
    by
      (intro
        synchronous.parallel_is_right_compatible_with_bisimilarity
        synchronous.repeated_receive_is_quasi_compatible_with_bisimilarity
      )
      simp
  also have "\<dots> \<sim>\<^sub>s \<currency>\<^sup>+ A \<parallel> (\<currency>\<^sup>? A \<parallel> B \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>? A \<parallel> (\<currency>\<^sup>+ A \<parallel> \<P> x)))"
    using thorn_simps
    by equivalence
  also have "\<dots> \<sim>\<^sub>s \<currency>\<^sup>+ A \<parallel> (\<currency>\<^sup>? A \<parallel> B \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>+ A \<parallel> \<P> x))"
    using inner_loss_redundancy
    by (rule synchronous.parallel_is_right_compatible_with_bisimilarity)
  also have "\<dots> \<sim>\<^sub>s \<currency>\<^sup>? A \<parallel> (\<currency>\<^sup>+ A \<parallel> B \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>+ A \<parallel> \<P> x))"
    using parallel_left_commutativity .
  also have "\<dots> \<sim>\<^sub>s \<currency>\<^sup>? A \<parallel> (\<currency>\<^sup>+ A \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x)"
    using inner_duplication_redundancy
    by (rule synchronous.parallel_is_right_compatible_with_bisimilarity)
  also have "\<dots> \<sim>\<^sub>s (\<currency>\<^sup>? A \<parallel> \<currency>\<^sup>+ A) \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x"
    using parallel_associativity
    by equivalence
  finally show ?thesis
  unfolding duploss_def .
qed

lemma send_idempotency_under_duploss:
  shows "\<currency>\<^sup>* A \<parallel> A \<triangleleft> X \<parallel> A \<triangleleft> X \<approx>\<^sub>s \<currency>\<^sup>* A \<parallel> A \<triangleleft> X"
proof (rule synchronous.mutual_silent_weak_transitions_up_to_bisimilarity)
  have "\<currency>\<^sup>? A \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>0\<^esup> X\<rparr> post_receive 0 X (\<lambda>_. \<zero> \<parallel> \<currency>\<^sup>? A)"
    unfolding loss_def and distributor_def and general_parallel.simps
    using receiving
    by (subst repeated_receive_proper_def)
  then have "\<currency>\<^sup>? A \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>0\<^esup> X\<rparr> \<zero> \<parallel> \<currency>\<^sup>? A"
    unfolding post_receive_after_parallel and post_receive_after_stop and post_receive_def
    by (transfer, simp)
  then have "\<currency>\<^sup>* A \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>0\<^esup> X\<rparr> (\<zero> \<parallel> \<currency>\<^sup>? A) \<parallel> \<currency>\<^sup>+ A"
    using parallel_left_io [where n = 0]
    by (transfer, simp)
  moreover have "A \<triangleleft> X \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>0\<^esup> X\<rparr> \<zero>"
    by (fact sending)
  then have "A \<triangleleft> X \<parallel> A \<triangleleft> X \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>0\<^esup> X\<rparr> A \<triangleleft> X \<parallel> \<zero>"
    using parallel_right_io [where n = 0]
    by (transfer, simp)
  ultimately have "\<currency>\<^sup>* A \<parallel> A \<triangleleft> X \<parallel> A \<triangleleft> X \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> ((\<zero> \<parallel> \<currency>\<^sup>? A) \<parallel> \<currency>\<^sup>+ A) \<parallel> A \<triangleleft> X \<parallel> \<zero>"
    using communication
    by fastforce
  then show "\<currency>\<^sup>* A \<parallel> A \<triangleleft> X \<parallel> A \<triangleleft> X \<Rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> ((\<zero> \<parallel> \<currency>\<^sup>? A) \<parallel> \<currency>\<^sup>+ A) \<parallel> A \<triangleleft> X \<parallel> \<zero>"
    by (fact synchronous.transition_in_weak_transition_rule)
next
  show "((\<zero> \<parallel> \<currency>\<^sup>? A) \<parallel> \<currency>\<^sup>+ A) \<parallel> A \<triangleleft> X \<parallel> \<zero> \<approx>\<^sub>s \<currency>\<^sup>* A \<parallel> A \<triangleleft> X"
    unfolding duploss_def
    using thorn_simps
    by equivalence
next
  have "\<currency>\<^sup>+ A \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>0\<^esup> X\<rparr> post_receive 0 X (\<lambda>x. (A \<triangleleft> \<box> x \<parallel> A \<triangleleft> \<box> x \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A)"
    unfolding duplication_def and distributor_def and general_parallel.simps
    using receiving
    by (subst repeated_receive_proper_def)
  then have "\<currency>\<^sup>+ A \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>0\<^esup> X\<rparr> (A \<triangleleft> X \<parallel> A \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A"
    unfolding post_receive_def
    by (transfer, simp)
  then have "\<currency>\<^sup>* A \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>0\<^esup> X\<rparr> \<currency>\<^sup>? A \<parallel> (A \<triangleleft> X \<parallel> A \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A"
    using parallel_right_io [where n = 0]
    by (transfer, simp)
  moreover have "A \<triangleleft> X \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>0\<^esup> X\<rparr> \<zero>"
    by (fact sending)
  ultimately have "\<currency>\<^sup>* A \<parallel> A \<triangleleft> X \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> (\<currency>\<^sup>? A \<parallel> (A \<triangleleft> X \<parallel> A \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A) \<parallel> \<zero>"
    using communication
    by fastforce
  then show "\<currency>\<^sup>* A \<parallel> A \<triangleleft> X \<Rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> (\<currency>\<^sup>? A \<parallel> (A \<triangleleft> X \<parallel> A \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A) \<parallel> \<zero>"
    by (fact synchronous.transition_in_weak_transition_rule)
next
  show "(\<currency>\<^sup>? A \<parallel> (A \<triangleleft> X \<parallel> A \<triangleleft> X \<parallel> \<zero>) \<parallel> \<currency>\<^sup>+ A) \<parallel> \<zero> \<approx>\<^sub>s \<currency>\<^sup>* A \<parallel> A \<triangleleft> X \<parallel> A \<triangleleft> X"
    unfolding duploss_def
    using thorn_simps
    by equivalence
qed

subsection \<open>Unidirectional Bridges\<close>

definition
  unidirectional_bridge :: "chan family \<Rightarrow> chan family \<Rightarrow> process family"
  (infix \<open>\<rightarrow>\<close> 52)
where
  [simp]: "A \<rightarrow> B = A \<Rightarrow> [B]"

lemma adapted_after_unidirectional_bridge:
  shows "(A \<rightarrow> B) \<guillemotleft> \<E> = A \<guillemotleft> \<E> \<rightarrow> B \<guillemotleft> \<E>"
  by (simp del: distributor_def add: adapted_after_distributor)

lemma transition_from_unidirectional_bridge:
  assumes "A \<rightarrow> B \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> Q"
  obtains n and X
    where
      "\<alpha> = A \<triangleright> \<star>\<^bsup>n\<^esup> X"
    and
      "Q = (B \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n"
  using assms unfolding unidirectional_bridge_def
  by (fastforce elim: transition_from_distributor)

lemma unidirectional_bridge_idempotency [thorn_simps]:
  shows "A \<rightarrow> B \<parallel> A \<rightarrow> B \<sim>\<^sub>s A \<rightarrow> B"
  unfolding unidirectional_bridge_def
  using distributor_idempotency .

lemma unidirectional_bridge_nested_idempotency [thorn_simps]:
  shows "A \<rightarrow> B \<parallel> (A \<rightarrow> B \<parallel> P) \<sim>\<^sub>s A \<rightarrow> B \<parallel> P"
  unfolding unidirectional_bridge_def
  using distributor_nested_idempotency .

lemma inner_unidirectional_bridge_redundancy:
  shows "A \<rightarrow> B \<parallel> C \<triangleright>\<^sup>\<infinity> x. (A \<rightarrow> B \<parallel> \<P> x) \<sim>\<^sub>s A \<rightarrow> B \<parallel> C \<triangleright>\<^sup>\<infinity> x. \<P> x"
  unfolding unidirectional_bridge_def
  using inner_distributor_redundancy .

context begin

private lemma adapted_unfolded_bridge_pullout:
  shows "
    ((B \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n) \<parallel> R \<guillemotleft> suffix n
    \<sim>\<^sub>s
    ((B \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>)) \<parallel> (A \<rightarrow> B \<parallel> R) \<guillemotleft> suffix n"
  unfolding adapted_after_parallel
  using thorn_simps
  by equivalence

lemma repeated_receive_shortcut_redundancy:
  shows "A \<rightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<approx>\<^sub>s A \<rightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x"
unfolding synchronous.weak_bisimilarity_is_mixed_bisimilarity
proof (coinduction rule: synchronous.mixed.up_to_rule [where \<F> = "[\<sim>\<^sub>s] \<frown> \<M> \<frown> [\<sim>\<^sub>s]"])
  case (forward_simulation \<alpha> S)
  then show ?case
  proof cases
    case (communication \<eta> \<mu> A' n X P Q)
    from \<open>A \<rightarrow> B \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> P\<close> have "\<eta> = Receiving"
      by (fastforce elim: transition_from_unidirectional_bridge)
    moreover
    from \<open>B \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<mu> A' n X\<rparr> Q\<close> have "\<mu> = Receiving"
      by (cases, auto elim: transition_from_repeated_receive)
    ultimately show ?thesis
      using \<open>\<eta> \<noteq> \<mu>\<close> by blast
  next
    case (parallel_left_communication P)
    then show ?thesis
      by (blast elim: transition_from_unidirectional_bridge)
  next
    case (parallel_right_communication Q)
    from \<open>B \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q\<close> show ?thesis
      by cases (fastforce elim: transition_from_repeated_receive)+
  next
    case (parallel_left_io \<eta> A' n X P)
    from \<open>A \<rightarrow> B \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> P\<close>
    have
      "\<eta> = Receiving"
    and
      "A' = A"
    and
      "P = (B \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n"
      by (blast elim: transition_from_unidirectional_bridge)+
    with \<open>A \<rightarrow> B \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> P\<close>
    have "A \<rightarrow> B \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> (B \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n"
      by (simp only:)
    then have "
      A \<rightarrow> B \<parallel> R \<Rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> ((B \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n) \<parallel> R \<guillemotleft> suffix n" for R
      by
        (intro
          synchronous_transition.parallel_left_io
          synchronous.transition_in_weak_transition_rule
        )
    then show ?thesis
      unfolding
        \<open>\<alpha> = IO \<eta> A' n X\<close> and \<open>S = P \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n\<close>
      and
        \<open>\<eta> = Receiving\<close> and \<open>A' = A\<close> and \<open>P = (B \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n\<close>
      using
        composition_in_universe
          [OF suffix_adapted_mutation_in_universe parallel_mutation_in_universe]
      and
        adapted_unfolded_bridge_pullout
      and
        adapted_unfolded_bridge_pullout [symmetric]
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  next
    case (parallel_right_io \<eta> C n X Q)
    from \<open>B \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> C n X\<rparr> Q\<close> show ?thesis
    proof cases
      case (parallel_left_io R)
      from \<open>B \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> C n X\<rparr> R\<close>
      have
        "\<eta> = Receiving"
      and
        "C = B"
      and
        "R = post_receive n X \<P> \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
        by (auto elim: transition_from_repeated_receive)
      with \<open>B \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> C n X\<rparr> R\<close>
      have B_transition: "B \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>B \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> post_receive n X \<P> \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
        by (simp only:)
      then have "
        B \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x
        \<rightarrow>\<^sub>s\<lparr>B \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
        (post_receive n X \<P> \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
        by (fact synchronous_transition.parallel_left_io)
      then have "
        A \<rightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x
        \<rightarrow>\<^sub>s\<lparr>B \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
        (A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> (post_receive n X \<P> \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
        by (fact synchronous_transition.parallel_right_io)
      moreover
      have "
        (A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> (post_receive n X \<P> \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n
        \<sim>\<^sub>s
        post_receive n X \<P> \<parallel> (A \<rightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
        unfolding adapted_after_parallel
        using thorn_simps
        by equivalence
      moreover
      from B_transition have "
        A \<rightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x
        \<Rightarrow>\<^sub>s\<lparr>B \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
        (A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> post_receive n X \<P> \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
        by
          (intro
            synchronous_transition.parallel_right_io
            synchronous.transition_in_weak_transition_rule
          )
      moreover
      have "
        post_receive n X \<P> \<parallel> (A \<rightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n
        \<sim>\<^sub>s
        (A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> post_receive n X \<P> \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
        unfolding adapted_after_parallel
        using thorn_simps
        by equivalence
      ultimately show ?thesis
        unfolding
          \<open>\<alpha> = IO \<eta> C n X\<close> and \<open>S = (A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> Q\<close>
        and
          \<open>\<eta> = Receiving\<close> and \<open>C = B\<close> and \<open>Q = R \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n\<close>
        and
          \<open>R = post_receive n X \<P> \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n\<close>
        using
          composition_in_universe
            [OF suffix_adapted_mutation_in_universe parallel_mutation_in_universe]
        by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
    next
      case (parallel_right_io R)
      from \<open>A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> C n X\<rparr> R\<close>
      have
        "\<eta> = Receiving"
      and
        "C = A"
      and
        "R = post_receive n X \<P> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
        by (auto elim: transition_from_repeated_receive)
      with \<open>A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> C n X\<rparr> R\<close>
      have A_transition: "A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> post_receive n X \<P> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
        by (simp only:)
      then have "
        A \<rightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x
        \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
        (A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n \<parallel> post_receive n X \<P> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
        by (intro synchronous_transition.parallel_right_io)
      moreover
      have "
        (A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n \<parallel> post_receive n X \<P> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n
        \<sim>\<^sub>s
        post_receive n X \<P> \<parallel> (A \<rightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
        unfolding adapted_after_parallel
        using thorn_simps
        by equivalence
      moreover
      have "
        A \<rightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x
        \<Rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
        ((\<zero> \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n) \<parallel> (post_receive n X \<P> \<parallel> B \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n)"
      proof -
        have "A \<rightarrow> B \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> post_receive n X (\<lambda>x. (B \<triangleleft> \<box> x \<parallel> \<zero>) \<parallel> A \<rightarrow> B)"
          unfolding unidirectional_bridge_def and distributor_def and general_parallel.simps
          using receiving
          by (subst repeated_receive_proper_def)
        then have "
          A \<rightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x
          \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
          post_receive n X (\<lambda>x. (B \<triangleleft> \<box> x \<parallel> \<zero>) \<parallel> A \<rightarrow> B) \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
          by (fact synchronous_transition.parallel_left_io)
        moreover have "
          post_receive n X (\<lambda>x. (B \<triangleleft> \<box> x \<parallel> \<zero>) \<parallel> A \<rightarrow> B) \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n
          =
          ((post_receive n X (\<lambda>x. B \<triangleleft> \<box> x) \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n) \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
          unfolding post_receive_after_parallel and post_receive_after_stop and post_receive_def ..
        then have "
          post_receive n X (\<lambda>x. (B \<triangleleft> \<box> x \<parallel> \<zero>) \<parallel> A \<rightarrow> B) \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n
          =
          ((B \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n) \<parallel> B \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n"
          unfolding post_receive_after_send and post_receive_def and adapted_after_repeated_receive
          by (transfer, simp)
        moreover have "
          ((B \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n) \<parallel> B \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n
          \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr>
          ((\<zero> \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n) \<parallel> (post_receive n X \<P> \<parallel> B \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n)"
        proof -
          have "
            ((B \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n)
            \<rightarrow>\<^sub>s\<lparr>B \<guillemotleft> suffix n \<triangleleft> \<star>\<^bsup>0\<^esup> X\<rparr>
            ((\<zero> \<parallel> \<zero> \<guillemotleft> suffix 0) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n \<guillemotleft> suffix 0)"
            by (intro sending parallel_left_io)
          moreover
          have "
            B \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n
            \<rightarrow>\<^sub>s\<lparr>B \<guillemotleft> suffix n \<triangleright> \<star>\<^bsup>0\<^esup> X\<rparr>
            post_receive 0 X (\<lambda>x. \<P> x \<guillemotleft> suffix n \<parallel> B \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n)"
            using receiving
            by (subst repeated_receive_proper_def)
          ultimately have "
            (((B \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n)) \<parallel> B \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n
            \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr>
            ((\<zero> \<parallel> \<zero> \<guillemotleft> suffix 0) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n \<guillemotleft> suffix 0) \<parallel>
            post_receive 0 X (\<lambda>x. \<P> x \<guillemotleft> suffix n \<parallel> B \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n)"
            using communication
            by fastforce
          then show ?thesis
            unfolding post_receive_def
            by (transfer, simp)
        qed
        ultimately show ?thesis
          by (simp, blast intro: rtranclp_trans)
      qed
      moreover have "
        post_receive n X \<P> \<parallel> (A \<rightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n
        \<sim>\<^sub>s
        ((\<zero> \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n) \<parallel> (post_receive n X \<P> \<parallel> B \<guillemotleft> suffix n \<triangleright>\<^sup>\<infinity> x. \<P> x \<guillemotleft> suffix n)"
        unfolding adapted_after_parallel and adapted_after_repeated_receive
        using thorn_simps
        by equivalence
      ultimately show ?thesis
        unfolding
          \<open>\<alpha> = IO \<eta> C n X\<close> and \<open>S = (A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> Q\<close>
        and
          \<open>\<eta> = Receiving\<close> and \<open>C = A\<close> and \<open>Q = (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n \<parallel> R\<close>
        and
          \<open>R = post_receive n X \<P> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n\<close>
        using
          composition_in_universe
            [OF suffix_adapted_mutation_in_universe parallel_mutation_in_universe]
        by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
    qed
  qed
next
  case (backward_simulation \<alpha> S)
  then show ?case
  proof cases
    case (parallel_left_io \<eta> A' n X P)
    from \<open>A \<rightarrow> B \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> P\<close>
    have
      "\<eta> = Receiving"
    and
      "A' = A"
    and
      "P = (B \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n"
      by (blast elim: transition_from_unidirectional_bridge)+
    with \<open>A \<rightarrow> B \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> P\<close>
    have "A \<rightarrow> B \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> (B \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n"
      by (simp only:)
    then have "
      A \<rightarrow> B \<parallel> R \<Rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> ((B \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n) \<parallel> R \<guillemotleft> suffix n" for R
      by
        (intro
          synchronous_transition.parallel_left_io
          synchronous.transition_in_weak_transition_rule
        )
    then show ?thesis
      unfolding
        \<open>\<alpha> = IO \<eta> A' n X\<close> and \<open>S = P \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n\<close>
      and
        \<open>\<eta> = Receiving\<close> and \<open>A' = A\<close> and \<open>P = (B \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n\<close>
      using
        adapted_unfolded_bridge_pullout
      and
        adapted_unfolded_bridge_pullout [symmetric]
      and
        composition_in_universe
          [OF suffix_adapted_mutation_in_universe parallel_mutation_in_universe]
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  next
    case (parallel_right_io \<eta> B' n X Q)
    from \<open>B \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> B' n X\<rparr> Q\<close>
    have
      "\<eta> = Receiving"
    and
      "B' = B"
    and
      "Q = post_receive n X \<P> \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
      by (auto elim: transition_from_repeated_receive)
    with \<open>B \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> B' n X\<rparr> Q\<close>
    have B_transition: "B \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>B \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> post_receive n X \<P> \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
      by (simp only:)
    then have "
      A \<rightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x
      \<rightarrow>\<^sub>s\<lparr>B \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
      (A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> post_receive n X \<P> \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
      by (fact synchronous_transition.parallel_right_io)
    moreover
    have "
      post_receive n X \<P> \<parallel> (A \<rightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n
      \<sim>\<^sub>s
      (A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> post_receive n X \<P> \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
      unfolding adapted_after_parallel
      using thorn_simps
      by equivalence
    moreover
    from B_transition have "
      A \<rightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x
      \<Rightarrow>\<^sub>s\<lparr>B \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>
      (A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> (post_receive n X \<P> \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
      by
        (intro
          synchronous_transition.parallel_right_io
          synchronous_transition.parallel_left_io
          synchronous.transition_in_weak_transition_rule
        )
    moreover
    have "
      (A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> (post_receive n X \<P> \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n
      \<sim>\<^sub>s
      post_receive n X \<P> \<parallel> (A \<rightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
      unfolding adapted_after_parallel
      using thorn_simps
      by equivalence
    ultimately show ?thesis
      unfolding
        \<open>\<alpha> = IO \<eta> B' n X\<close> and \<open>S = (A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> Q\<close>
      and
        \<open>\<eta> = Receiving\<close> and \<open>B' = B\<close> and \<open>Q = post_receive n X \<P> \<parallel> (B \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n\<close>
      using
        composition_in_universe
          [OF suffix_adapted_mutation_in_universe parallel_mutation_in_universe]
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  qed (auto elim: transition_from_repeated_receive)
qed respectful

end

lemma distributor_shortcut_redundancy:
  shows "A \<rightarrow> B \<parallel> B \<Rightarrow> Cs \<parallel> A \<Rightarrow> Cs \<approx>\<^sub>s A \<rightarrow> B \<parallel> B \<Rightarrow> Cs"
  unfolding distributor_def
  using repeated_receive_shortcut_redundancy .

lemma unidirectional_bridge_shortcut_redundancy:
  shows "A \<rightarrow> B \<parallel> B \<rightarrow> C \<parallel> A \<rightarrow> C \<approx>\<^sub>s A \<rightarrow> B \<parallel> B \<rightarrow> C"
  using distributor_shortcut_redundancy
  unfolding unidirectional_bridge_def .

lemma loop_redundancy_under_duploss:
  shows "\<currency>\<^sup>* A \<parallel> A \<rightarrow> A \<approx>\<^sub>s \<currency>\<^sup>* A"
  sorry

lemma sidetrack_redundancy:
  shows "\<Prod>B \<leftarrow> Bs. \<currency>\<^sup>? B \<parallel> A \<Rightarrow> (B\<^sub>0 # Bs) \<parallel> A \<rightarrow> B\<^sub>0 \<approx>\<^sub>s \<Prod>B \<leftarrow> Bs. \<currency>\<^sup>? B \<parallel> A \<Rightarrow> (B\<^sub>0 # Bs)"
  sorry

lemma distributor_split:
  shows "\<currency>\<^sup>+ A \<parallel> \<Prod>B \<leftarrow> Bs. \<currency>\<^sup>? B \<parallel> A \<Rightarrow> Bs \<approx>\<^sub>s \<currency>\<^sup>+ A \<parallel> \<Prod>B \<leftarrow> Bs. \<currency>\<^sup>? B \<parallel> \<Prod>B \<leftarrow> Bs. A \<rightarrow> B"
  sorry

subsection \<open>Bidirectional Bridges\<close>

definition
  bidirectional_bridge :: "chan family \<Rightarrow> chan family \<Rightarrow> process family"
  (infix \<open>\<leftrightarrow>\<close> 52)
where
  [simp]: "A \<leftrightarrow> B = A \<rightarrow> B \<parallel> B \<rightarrow> A"

lemma adapted_after_bidirectional_bridge:
  shows "(A \<leftrightarrow> B) \<guillemotleft> \<E> = A \<guillemotleft> \<E> \<leftrightarrow> B \<guillemotleft> \<E>"
  by (simp only: bidirectional_bridge_def adapted_after_parallel adapted_after_unidirectional_bridge)

lemma bidirectional_bridge_idempotency [thorn_simps]:
  shows "A \<leftrightarrow> B \<parallel> A \<leftrightarrow> B \<sim>\<^sub>s A \<leftrightarrow> B"
  unfolding bidirectional_bridge_def
  using thorn_simps
  by equivalence

lemma bidirectional_bridge_nested_idempotency [thorn_simps]:
  shows "A \<leftrightarrow> B \<parallel> (A \<leftrightarrow> B \<parallel> P) \<sim>\<^sub>s A \<leftrightarrow> B \<parallel> P"
  unfolding bidirectional_bridge_def
  using thorn_simps
  by equivalence

lemma inner_bidirectional_bridge_redundancy:
  shows "A \<leftrightarrow> B \<parallel> C \<triangleright>\<^sup>\<infinity> x. (A \<leftrightarrow> B \<parallel> \<P> x) \<sim>\<^sub>s A \<leftrightarrow> B \<parallel> C \<triangleright>\<^sup>\<infinity> x. \<P> x"
proof -
  have "
    post_receive n X (\<lambda>x. (A \<rightarrow> B \<parallel> B \<rightarrow> A) \<parallel> \<P> x)
    \<sim>\<^sub>s
    post_receive n X (\<lambda>x. A \<rightarrow> B \<parallel> (B \<rightarrow> A \<parallel> \<P> x))"
    for n and X
  proof -
    have "
      (\<lambda>e. (((A \<rightarrow> B \<parallel> B \<rightarrow> A) \<parallel> \<P> (X e)) \<guillemotleft> suffix n) e)
      =
      (\<lambda>e. (((A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> (B \<rightarrow> A) \<guillemotleft> suffix n) \<parallel> \<P> (X e) \<guillemotleft> suffix n) e)"
      by (simp only: adapted_after_parallel)
    also have "\<dots> = ((A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> (B \<rightarrow> A) \<guillemotleft> suffix n) \<parallel> (\<lambda>e. (\<P> (X e) \<guillemotleft> suffix n) e)"
      by (subst environment_dependent_parallel) (fact refl)
    also have "\<dots> \<sim>\<^sub>s (A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> ((B \<rightarrow> A) \<guillemotleft> suffix n \<parallel> (\<lambda>e. (\<P> (X e) \<guillemotleft> suffix n) e))"
      using parallel_associativity .
    also have "\<dots> = (\<lambda>e. ((A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> ((B \<rightarrow> A) \<guillemotleft> suffix n \<parallel> \<P> (X e) \<guillemotleft> suffix n)) e)"
      by
        (subst (3) environment_dependent_parallel, subst (4) environment_dependent_parallel)
        (fact refl)
    also have "\<dots> = (\<lambda>e. ((A \<rightarrow> B \<parallel> (B \<rightarrow> A \<parallel> \<P> (X e))) \<guillemotleft> suffix n) e)"
      by (simp only: adapted_after_parallel)
    finally show ?thesis
      unfolding post_receive_def .
  qed
  then have "
    (A \<rightarrow> B \<parallel> B \<rightarrow> A) \<parallel> C \<triangleright>\<^sup>\<infinity> x. ((A \<rightarrow> B \<parallel> B \<rightarrow> A) \<parallel> \<P> x)
    \<sim>\<^sub>s
    (A \<rightarrow> B \<parallel> B \<rightarrow> A) \<parallel> C \<triangleright>\<^sup>\<infinity> x. (A \<rightarrow> B \<parallel> (B \<rightarrow> A \<parallel> \<P> x))"
    by
      (intro
        synchronous.parallel_is_right_compatible_with_bisimilarity
        synchronous.repeated_receive_is_quasi_compatible_with_bisimilarity
      )
      simp
  also have "\<dots> \<sim>\<^sub>s B \<rightarrow> A \<parallel> (A \<rightarrow> B \<parallel> C \<triangleright>\<^sup>\<infinity> x. (A \<rightarrow> B \<parallel> (B \<rightarrow> A \<parallel> \<P> x)))"
    using thorn_simps
    by equivalence
  also have "\<dots> \<sim>\<^sub>s B \<rightarrow> A \<parallel> (A \<rightarrow> B \<parallel> C \<triangleright>\<^sup>\<infinity> x. (B \<rightarrow> A \<parallel> \<P> x))"
    using inner_unidirectional_bridge_redundancy
    by (rule synchronous.parallel_is_right_compatible_with_bisimilarity)
  also have "\<dots> \<sim>\<^sub>s A \<rightarrow> B \<parallel> (B \<rightarrow> A \<parallel> C \<triangleright>\<^sup>\<infinity> x. (B \<rightarrow> A \<parallel> \<P> x))"
    using parallel_left_commutativity .
  also have "\<dots> \<sim>\<^sub>s A \<rightarrow> B \<parallel> (B \<rightarrow> A \<parallel> C \<triangleright>\<^sup>\<infinity> x. \<P> x)"
    using inner_unidirectional_bridge_redundancy
    by (rule synchronous.parallel_is_right_compatible_with_bisimilarity)
  also have "\<dots> \<sim>\<^sub>s (A \<rightarrow> B \<parallel> B \<rightarrow> A) \<parallel> C \<triangleright>\<^sup>\<infinity> x. \<P> x"
    using thorn_simps
    by equivalence
  finally show ?thesis
    unfolding bidirectional_bridge_def .
qed

lemma bidirectional_bridge_commutativity [thorn_simps]:
  shows "A \<leftrightarrow> B \<sim>\<^sub>s B \<leftrightarrow> A"
  unfolding bidirectional_bridge_def
  using parallel_commutativity .

lemma forward_bridge_absorption:
  shows "A \<leftrightarrow> B \<parallel> A \<rightarrow> B \<sim>\<^sub>s A \<leftrightarrow> B"
  unfolding bidirectional_bridge_def
  using thorn_simps
  by equivalence

lemma backward_bridge_absorption:
  shows "A \<leftrightarrow> B \<parallel> B \<rightarrow> A \<sim>\<^sub>s A \<leftrightarrow> B"
  unfolding bidirectional_bridge_def
  using thorn_simps
  by equivalence

context begin

(* TODO: Perhaps reuse in other proofs *)
private lemma transition_from_unidirectional_bridge_construction:
  shows "A \<rightarrow> B \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> (B \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<zero>) \<parallel> (A \<rightarrow> B) \<guillemotleft> suffix n" (is "?S \<rightarrow>\<^sub>s\<lparr>_\<rparr> ?T")
proof -
  have "?S \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> post_receive n X (\<lambda>x. (B \<triangleleft> \<box> x \<parallel> \<zero>) \<parallel> A \<rightarrow> B)"
    unfolding unidirectional_bridge_def and distributor_def and general_parallel.simps
    using receiving
    by (subst repeated_receive_proper_def)
  moreover have "post_receive n X (\<lambda>x. (B \<triangleleft> \<box> x \<parallel> \<zero>) \<parallel> A \<rightarrow> B) = ?T"
    unfolding post_receive_def
    by (transfer, simp)
  ultimately show ?thesis
    by (simp only:)
qed

lemma send_channel_switch:
  shows "A \<leftrightarrow> B \<parallel> A \<triangleleft> X \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<triangleleft> X"
proof (rule synchronous.mutual_silent_weak_transitions_up_to_bisimilarity)
  have "A \<rightarrow> B \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>0\<^esup> X\<rparr> (B \<triangleleft> X \<parallel> \<zero>) \<parallel> A \<rightarrow> B"
    using transition_from_unidirectional_bridge_construction [where n = 0]
    by (transfer, simp)
  then have "A \<leftrightarrow> B \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>0\<^esup> X\<rparr> ((B \<triangleleft> X \<parallel> \<zero>) \<parallel> A \<rightarrow> B) \<parallel> B \<rightarrow> A"
    using parallel_left_io [where n = 0]
    by (transfer, simp)
  moreover have "A \<triangleleft> X \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>0\<^esup> X\<rparr> \<zero>"
    by (fact sending)
  ultimately show "A \<leftrightarrow> B \<parallel> A \<triangleleft> X \<Rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> (((B \<triangleleft> X \<parallel> \<zero>) \<parallel> A \<rightarrow> B) \<parallel> B \<rightarrow> A) \<parallel> \<zero>"
    using communication
    by fastforce
next
  show "(((B \<triangleleft> X \<parallel> \<zero>) \<parallel> A \<rightarrow> B) \<parallel> B \<rightarrow> A) \<parallel> \<zero> \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<triangleleft> X"
    unfolding bidirectional_bridge_def
    using thorn_simps
    by equivalence
next
  have "B \<rightarrow> A \<rightarrow>\<^sub>s\<lparr>B \<triangleright> \<star>\<^bsup>0\<^esup> X\<rparr> (A \<triangleleft> X \<parallel> \<zero>) \<parallel> B \<rightarrow> A"
    using transition_from_unidirectional_bridge_construction [where n = 0]
    by (transfer, simp)
  then have "A \<leftrightarrow> B \<rightarrow>\<^sub>s\<lparr>B \<triangleright> \<star>\<^bsup>0\<^esup> X\<rparr> A \<rightarrow> B \<parallel> (A \<triangleleft> X \<parallel> \<zero>) \<parallel> B \<rightarrow> A"
    using parallel_right_io [where n = 0]
    by (transfer, simp)
  moreover have "B \<triangleleft> X \<rightarrow>\<^sub>s\<lparr>B \<triangleleft> \<star>\<^bsup>0\<^esup> X\<rparr> \<zero>"
    by (fact sending)
  ultimately show "A \<leftrightarrow> B \<parallel> B \<triangleleft> X \<Rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> (A \<rightarrow> B \<parallel> (A \<triangleleft> X \<parallel> \<zero>) \<parallel> B \<rightarrow> A) \<parallel> \<zero>"
    using communication
    by fastforce
next
  show "(A \<rightarrow> B \<parallel> (A \<triangleleft> X \<parallel> \<zero>) \<parallel> B \<rightarrow> A) \<parallel> \<zero> \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> A \<triangleleft> X"
    unfolding bidirectional_bridge_def
    using thorn_simps
    by equivalence
qed

end

lemma receive_channel_switch:
  shows "A \<leftrightarrow> B \<parallel> A \<triangleright> x. \<P> x \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<triangleright> x. \<P> x"
  sorry

lemma general_parallel_channel_switch:
  assumes "\<And>x. fst x \<leftrightarrow> snd x \<parallel> \<P> (fst x) \<approx>\<^sub>s fst x \<leftrightarrow> snd x \<parallel> \<P> (snd x)"
  shows "\<Prod>v \<leftarrow> vs. fst v \<leftrightarrow> snd v \<parallel> \<Prod>v \<leftarrow> vs. \<P> (fst v) \<approx>\<^sub>s \<Prod>v \<leftarrow> vs. fst v \<leftrightarrow> snd v \<parallel> \<Prod>v \<leftarrow> vs. \<P> (snd v)"
proof (induction vs)
  case Nil
  show ?case
    unfolding general_parallel.simps(1)
    by equivalence
next
  case (Cons v vs)
  have "
    (fst v \<leftrightarrow> snd v \<parallel> \<Prod>v \<leftarrow> vs. fst v \<leftrightarrow> snd v) \<parallel> \<P> (fst v) \<parallel> \<Prod>x \<leftarrow> vs. \<P> (fst x)
    \<approx>\<^sub>s
    (fst v \<leftrightarrow> snd v \<parallel> \<P> (fst v)) \<parallel> (\<Prod>x \<leftarrow> vs. fst x \<leftrightarrow> snd x \<parallel> \<Prod>x \<leftarrow> vs. \<P> (fst x))"
    using thorn_simps
    by equivalence
  also have "\<dots> \<approx>\<^sub>s (fst v \<leftrightarrow> snd v \<parallel> \<P> (snd v)) \<parallel> (\<Prod>v \<leftarrow> vs. fst v \<leftrightarrow> snd v \<parallel> \<Prod>v \<leftarrow> vs. \<P> (snd v))"
    using assms and Cons.IH
    by (rule synchronous.weak.parallel_is_compatible_with_bisimilarity)
  also have "\<dots> \<approx>\<^sub>s (fst v \<leftrightarrow> snd v \<parallel> \<Prod>v \<leftarrow> vs. fst v \<leftrightarrow> snd v) \<parallel> (\<P> (snd v) \<parallel> \<Prod>v \<leftarrow> vs. \<P> (snd v))"
    using thorn_simps
    by equivalence
  finally show ?case
    unfolding general_parallel.simps(2) .
qed

lemma repeated_receive_channel_switch:
  shows "A \<leftrightarrow> B \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x"
  sorry

lemma distributor_source_switch:
  shows "A \<leftrightarrow> B \<parallel> A \<Rightarrow> Cs \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<Rightarrow> Cs"
  unfolding distributor_def
  using repeated_receive_channel_switch .

(*FIXME:
  Simplify the proof of the following lemma once #231 is resolved.

  In particular, do the following:

    \<^item> Turn the detailed proofs that involve
      \<^theory_text>\<open>repeated_receive_is_quasi_compatible_with_synchronous_bisimilarity\<close> into single-step proofs
      that use the \<^theory_text>\<open>bisimilarity\<close> proof method.

    \<^item> Merge the resulting proofs with adjacent proofs if \<^theory_text>\<open>bisimilarity\<close> can solve the whole step.

    \<^item> Merge applications of \<^theory_text>\<open>parallel_commutativity\<close> and \<^theory_text>\<open>parallel_associativity\<close> when possible.

    \<^item> Get rid of applications of compatibility rules whenever \<^theory_text>\<open>bisimilarity\<close> can be used instead.
*)
(*FIXME:
  The following proof uses \<^theory_text>\<open>general_parallel_conversion_deferral\<close> twice. Check whether this is
  unnecessary and, if yes, whether it should be avoided.
*)
lemma distributor_target_switch:
  shows
    "\<Prod>v \<leftarrow> vs. fst v \<leftrightarrow> snd v \<parallel> A \<Rightarrow> map fst vs \<approx>\<^sub>s \<Prod>v \<leftarrow> vs. fst v \<leftrightarrow> snd v \<parallel> A \<Rightarrow> map snd vs"
    (is "?\<P> vs \<parallel> _ \<approx>\<^sub>s ?\<P> vs \<parallel> _")
proof -
  \<comment> \<open>Specializations of lemmas:\<close>
  have inner_target_bridges_redundancy:
    "?\<P> vs \<parallel> A \<triangleright>\<^sup>\<infinity> y. (?\<P> vs \<parallel> \<Q> y) \<sim>\<^sub>s ?\<P> vs \<parallel> A \<triangleright>\<^sup>\<infinity> y. \<Q> y" for \<Q>
    using inner_bidirectional_bridge_redundancy
    by (rule inner_general_parallel_redundancy)
  have targets_switch:
    "?\<P> ws \<parallel> \<Prod>w \<leftarrow> ws. fst w \<triangleleft> Y \<approx>\<^sub>s ?\<P> ws \<parallel> \<Prod>w \<leftarrow> ws. snd w \<triangleleft> Y" for ws and Y
    using send_channel_switch
    by (rule general_parallel_channel_switch)
  have post_receive_targets_switch: "
    post_receive n X (\<lambda>x. ?\<P> vs \<parallel> \<Prod>v \<leftarrow> vs. fst v \<triangleleft> \<box> x)
    \<approx>\<^sub>s
    post_receive n X (\<lambda>x. ?\<P> vs \<parallel> \<Prod>v \<leftarrow> vs. snd v \<triangleleft> \<box> x)"
    for n and X
  proof -
    let ?ws = "map (\<lambda>v. (fst v \<guillemotleft> suffix n, snd v \<guillemotleft> suffix n)) vs"
    have "
      (\<lambda>e. ((?\<P> vs \<parallel> \<Prod>v \<leftarrow> vs. fst v \<triangleleft> \<box> (X e)) \<guillemotleft> suffix n) e)
      =
      (\<lambda>e. (\<Prod>v \<leftarrow> vs. fst v \<guillemotleft> suffix n \<leftrightarrow> snd v \<guillemotleft> suffix n \<parallel> \<Prod>v \<leftarrow> vs. fst v \<guillemotleft> suffix n \<triangleleft> \<box> (X e) \<guillemotleft> suffix n) e)"
      by
        (simp only:
          adapted_after_parallel
          adapted_after_general_parallel
          adapted_after_bidirectional_bridge
          adapted_after_send
        )
    also have "\<dots> = \<Prod>v \<leftarrow> vs. fst v \<guillemotleft> suffix n \<leftrightarrow> snd v \<guillemotleft> suffix n \<parallel> \<Prod>v \<leftarrow> vs. fst v \<guillemotleft> suffix n \<triangleleft> X"
      by
        (
          subst environment_dependent_parallel,
          subst (2) environment_dependent_general_parallel,
          subst environment_dependent_send,
          transfer,
          simp only: comp_def constant_family_def
        )
    also have "\<dots> = \<Prod>w \<leftarrow> ?ws. fst w \<leftrightarrow> snd w \<parallel> \<Prod>w \<leftarrow> ?ws. fst w \<triangleleft> X"
      by (simp only: general_parallel_conversion_deferral fst_conv snd_conv)
    also have "\<dots> \<approx>\<^sub>s \<Prod>w \<leftarrow> ?ws. fst w \<leftrightarrow> snd w \<parallel> \<Prod>w \<leftarrow> ?ws. snd w \<triangleleft> X"
      using general_parallel_channel_switch [OF send_channel_switch] .
    also have "\<dots> = \<Prod>v \<leftarrow> vs. fst v \<guillemotleft> suffix n \<leftrightarrow> snd v \<guillemotleft> suffix n \<parallel> \<Prod>v \<leftarrow> vs. snd v \<guillemotleft> suffix n \<triangleleft> X"
      by (simp only: general_parallel_conversion_deferral fst_conv snd_conv)
    also have "\<dots> = (\<lambda>e. (\<Prod>v \<leftarrow> vs. fst v \<guillemotleft> suffix n \<leftrightarrow> snd v \<guillemotleft> suffix n \<parallel> \<Prod>v \<leftarrow> vs. snd v \<guillemotleft> suffix n \<triangleleft> \<box> (X e) \<guillemotleft> suffix n) e)"
      by
        (
          subst (2) environment_dependent_parallel,
          subst (4) environment_dependent_general_parallel,
          subst (2) environment_dependent_send,
          transfer,
          simp only: comp_def constant_family_def
        )
    also have "\<dots> = (\<lambda>e. ((?\<P> vs \<parallel> \<Prod>v \<leftarrow> vs. snd v \<triangleleft> \<box> (X e)) \<guillemotleft> suffix n) e)"
      by
        (simp only:
          adapted_after_parallel
          adapted_after_general_parallel
          adapted_after_bidirectional_bridge
          adapted_after_send
        )
    finally show ?thesis
      unfolding post_receive_def .
  qed
  \<comment> \<open>The actual proof:\<close>
  have "?\<P> vs \<parallel> A \<triangleright>\<^sup>\<infinity> y. \<Prod>v \<leftarrow> vs. fst v \<triangleleft> \<box> y \<approx>\<^sub>s ?\<P> vs \<parallel> A \<triangleright>\<^sup>\<infinity> y. (?\<P> vs \<parallel> \<Prod>v \<leftarrow> vs. fst v \<triangleleft> \<box> y)"
    by
      (
        rule synchronous.bisimilarity_in_weak_bisimilarity [THEN predicate2D],
        rule synchronous.bisimilarity_symmetry_rule
      )
      (fact inner_target_bridges_redundancy)
  also have "\<dots> \<approx>\<^sub>s ?\<P> vs \<parallel> A \<triangleright>\<^sup>\<infinity> y. (?\<P> vs \<parallel> \<Prod>v \<leftarrow> vs. snd v \<triangleleft> \<box> y)"
    using post_receive_targets_switch
    by
      (intro
        synchronous.weak.parallel_is_right_compatible_with_bisimilarity
        synchronous.weak.repeated_receive_is_quasi_compatible_with_bisimilarity
      )
      simp
  also have "\<dots> \<approx>\<^sub>s ?\<P> vs \<parallel> A \<triangleright>\<^sup>\<infinity> y. \<Prod>v \<leftarrow> vs. snd v \<triangleleft> \<box> y"
    by
      (rule synchronous.bisimilarity_in_weak_bisimilarity [THEN predicate2D])
      (fact inner_target_bridges_redundancy)
  finally show ?thesis
    unfolding distributor_def and general_parallel_conversion_deferral .
qed

lemma loss_channel_switch:
  shows "A \<leftrightarrow> B \<parallel> \<currency>\<^sup>? A \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> \<currency>\<^sup>? B"
  unfolding loss_def using distributor_source_switch .

lemma duplication_channel_switch:
  shows "A \<leftrightarrow> B \<parallel> \<currency>\<^sup>+ A \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> \<currency>\<^sup>+ B"
proof -
  have "A \<leftrightarrow> B \<parallel> A \<Rightarrow> [A, A] \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<Rightarrow> [A, A]"
    using distributor_source_switch .
  also have "\<dots> \<approx>\<^sub>s (A \<leftrightarrow> B \<parallel> A \<leftrightarrow> B \<parallel> \<zero>) \<parallel> B \<Rightarrow> [A, A]"
    using thorn_simps
    by equivalence
  also have "\<dots> \<approx>\<^sub>s \<Prod>v \<leftarrow> [(A, B), (A, B)]. fst v \<leftrightarrow> snd v \<parallel> B \<Rightarrow> map fst [(A, B), (A, B)]"
    by simp
  also have "\<dots> \<approx>\<^sub>s \<Prod>v \<leftarrow> [(A, B), (A, B)]. fst v \<leftrightarrow> snd v \<parallel> B \<Rightarrow> map snd [(A, B), (A, B)]"
    using distributor_target_switch .
  also have "\<dots> \<approx>\<^sub>s (A \<leftrightarrow> B \<parallel> A \<leftrightarrow> B \<parallel> \<zero>) \<parallel> B \<Rightarrow> [B, B]"
    by simp
  also have "\<dots> \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<Rightarrow> [B, B]"
    using thorn_simps
    by equivalence
  finally show ?thesis
    unfolding duplication_def .
qed

lemma duploss_channel_switch:
  shows "A \<leftrightarrow> B \<parallel> \<currency>\<^sup>* A \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> \<currency>\<^sup>* B"
proof -
  have "A \<leftrightarrow> B \<parallel> (\<currency>\<^sup>? A \<parallel> \<currency>\<^sup>+ A) \<approx>\<^sub>s (A \<leftrightarrow> B \<parallel> \<currency>\<^sup>? A) \<parallel> \<currency>\<^sup>+ A"
    using thorn_simps
    by equivalence
  also have "\<dots> \<approx>\<^sub>s (A \<leftrightarrow> B \<parallel> \<currency>\<^sup>? B) \<parallel> \<currency>\<^sup>+ A"
    using loss_channel_switch
    by (rule synchronous.weak.parallel_is_left_compatible_with_bisimilarity)
  also have "\<dots> \<approx>\<^sub>s \<currency>\<^sup>? B \<parallel> (A \<leftrightarrow> B \<parallel> \<currency>\<^sup>+ A)"
    using thorn_simps
    by equivalence
  also have "\<dots> \<approx>\<^sub>s \<currency>\<^sup>? B \<parallel> (A \<leftrightarrow> B \<parallel> \<currency>\<^sup>+ B)"
    using duplication_channel_switch
    by (rule synchronous.weak.parallel_is_right_compatible_with_bisimilarity)
  also have "\<dots> \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> (\<currency>\<^sup>? B \<parallel> \<currency>\<^sup>+ B)"
    using thorn_simps
    by equivalence
  finally show ?thesis
    unfolding duploss_def .
qed

lemma unidirectional_bridge_source_switch:
  shows "A \<leftrightarrow> B \<parallel> A \<rightarrow> C \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<rightarrow> C"
  unfolding unidirectional_bridge_def
  using distributor_source_switch .

lemma unidirectional_bridge_target_switch:
  shows "A \<leftrightarrow> B \<parallel> C \<rightarrow> A \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> C \<rightarrow> B"
proof -
  have "A \<leftrightarrow> B \<parallel> C \<Rightarrow> [A] \<approx>\<^sub>s (A \<leftrightarrow> B \<parallel> \<zero>) \<parallel> C \<Rightarrow> [A]"
    using thorn_simps
    by equivalence
  also have "\<dots> \<approx>\<^sub>s \<Prod>v \<leftarrow> [(A, B)]. fst v \<leftrightarrow> snd v \<parallel> C \<Rightarrow> map fst [(A, B)]"
    by simp
  also have "\<dots> \<approx>\<^sub>s \<Prod>v \<leftarrow>[(A, B)]. fst v \<leftrightarrow> snd v \<parallel> C \<Rightarrow> map snd [(A, B)]"
    using distributor_target_switch .
  also have "\<dots> \<approx>\<^sub>s (A \<leftrightarrow> B \<parallel> \<zero>) \<parallel> C \<Rightarrow> [B]"
    by simp
  also have "\<dots> \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> C \<Rightarrow> [B]"
    using thorn_simps
    by equivalence
  finally show ?thesis
    unfolding unidirectional_bridge_def .
qed

lemma bidirectional_bridge_source_switch:
  shows "A \<leftrightarrow> B \<parallel> A \<leftrightarrow> C \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<leftrightarrow> C"
proof -
  have "A \<leftrightarrow> B \<parallel> (A \<rightarrow> C \<parallel> C \<rightarrow> A) \<approx>\<^sub>s (A \<leftrightarrow> B \<parallel> A \<rightarrow> C) \<parallel> C \<rightarrow> A"
    using thorn_simps
    by equivalence
  also have "\<dots> \<approx>\<^sub>s (A \<leftrightarrow> B \<parallel> B \<rightarrow> C) \<parallel> C \<rightarrow> A"
    using unidirectional_bridge_source_switch
    by (rule synchronous.weak.parallel_is_left_compatible_with_bisimilarity)
  also have "\<dots> \<approx>\<^sub>s B \<rightarrow> C \<parallel> (A \<leftrightarrow> B \<parallel> C \<rightarrow> A)"
    using thorn_simps
    by equivalence
  also have "\<dots> \<approx>\<^sub>s B \<rightarrow> C \<parallel> (A \<leftrightarrow> B \<parallel> C \<rightarrow> B)"
    using unidirectional_bridge_target_switch
    by (rule synchronous.weak.parallel_is_right_compatible_with_bisimilarity)
  also have "\<dots> \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> (B \<rightarrow> C \<parallel> C \<rightarrow> B)"
    using thorn_simps
    by equivalence
  finally show ?thesis
    unfolding bidirectional_bridge_def .
qed

lemma bidirectional_bridge_target_switch:
  shows "A \<leftrightarrow> B \<parallel> C \<leftrightarrow> A \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> C \<leftrightarrow> B"
proof -
  have "A \<leftrightarrow> B \<parallel> C \<leftrightarrow> A \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> A \<leftrightarrow> C"
    using bidirectional_bridge_commutativity
    by equivalence
  also have "\<dots> \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<leftrightarrow> C"
    using bidirectional_bridge_source_switch .
  also have "\<dots> \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> C \<leftrightarrow> B"
    using bidirectional_bridge_commutativity
    by equivalence
  finally show ?thesis .
qed

lemma detour_squashing:
  shows "\<nu> b. (A \<leftrightarrow> \<box> b) \<approx>\<^sub>s A \<rightarrow> A"
  sorry

(*FIXME:
  Use \<^theory_text>\<open>equivalence\<close> and possible similar proof methods in the following proof once this is possible
  with higher operators like \<open>\<leftrightarrow>\<close>.
*)
lemma duploss_detour_collapse:
  shows "\<nu> b. (\<currency>\<^sup>* (\<box> b) \<parallel> A \<leftrightarrow> \<box> b) \<approx>\<^sub>s \<currency>\<^sup>* A"
proof -
  have "\<nu> b. (\<currency>\<^sup>* (\<box> b) \<parallel> A \<leftrightarrow> \<box> b) \<approx>\<^sub>s \<nu> b. (\<box> b \<leftrightarrow> A \<parallel> \<currency>\<^sup>* (\<box> b))"
    using thorn_simps
    sorry
  also have "\<dots> \<approx>\<^sub>s \<nu> b. (\<box> b \<leftrightarrow> A \<parallel> \<currency>\<^sup>* A)"
    using duploss_channel_switch
    sorry
  also have "\<dots> \<approx>\<^sub>s \<currency>\<^sup>* A \<parallel> \<nu> b. (A \<leftrightarrow> \<box> b)"
    using thorn_simps
    sorry
  also have "\<dots> \<approx>\<^sub>s \<currency>\<^sup>* A \<parallel> A \<rightarrow> A"
    using detour_squashing
    sorry
  also have "\<dots> \<approx>\<^sub>s \<currency>\<^sup>* A"
    using loop_redundancy_under_duploss
    by equivalence
  finally show ?thesis .
qed

end
