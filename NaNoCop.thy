theory NaNoCop imports Main
begin

primrec member (infix\<open>|\<in>|\<close> 200) where
  \<open>(_ |\<in>| []) = False\<close> |
  \<open>(x |\<in>| (x' # xs)) = ((x = x') \<or> (x |\<in>| xs))\<close>

lemma member_simp[simp]: \<open>x |\<in>| xs \<longleftrightarrow> x \<in> (set xs)\<close> 
  by (induct xs) simp_all

abbreviation notmember (infix \<open>|\<notin>|\<close> 200) where \<open>x |\<notin>| xs \<equiv> \<not> x |\<in>| xs\<close>

definition \<open>linsert x xs \<equiv> (if (x |\<in>| xs) then xs else x # xs)\<close>

lemma linsert_is_insert: \<open>set (linsert x xs) = insert x (set xs)\<close>
  by (induct xs) (simp_all add: linsert_def insert_absorb)

primrec subseteq (infix \<open>|\<subseteq>|\<close> 120) where
  \<open>([] |\<subseteq>| _) = True\<close> |
  \<open>((x # xs) |\<subseteq>| ys) = ((x |\<in>| ys) \<and> (xs |\<subseteq>| ys))\<close>

lemma subseteq_simp[simp]: \<open>xs |\<subseteq>| ys \<longleftrightarrow> (set xs) \<subseteq> (set ys)\<close> 
  by (induct xs) simp_all

primrec lremove where
  \<open>lremove _ [] = []\<close> |
  \<open>lremove x (y # ys) = (if y = x then lremove x ys else y # (lremove x ys))\<close>

lemma lremove_simp[simp]: \<open>set (lremove x xs) = (set xs) - {x}\<close>
  by (induct xs) (simp_all add: insert_Diff_if)
  
primrec lminus (infix \<open>|-|\<close> 210) where
  \<open>xs |-| [] = xs\<close> |
  \<open>xs |-| (y # ys) = (lremove y xs) |-| ys\<close>

lemma hoist_lremove:\<open>set ((lremove x xs) |-| ys) = set (lremove x (xs |-| ys))\<close> 
  apply (induct ys arbitrary: x xs)
   apply simp
  by (metis Diff_insert Diff_insert2 lminus.simps(2) lremove_simp)

lemma lminus_simp[simp]: \<open>set (xs |-| ys) = (set xs) - (set ys)\<close>
proof (induct ys)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  have \<open>set (xs |-| (y # ys)) = set (xs |-| ys) - {y}\<close>
    by (simp add: hoist_lremove)
  then show ?case
    using Cons.hyps by force
qed

definition lequal (infix \<open>|=|\<close> 120) where \<open>xs |=| ys \<equiv> xs |\<subseteq>| ys \<and> ys |\<subseteq>| xs\<close>

lemma lequal_simp[simp]: \<open>xs |=| ys \<longleftrightarrow> (set xs) = (set ys)\<close>
  by (simp add: lequal_def set_eq_subset)

primrec lunion (infix \<open>|\<union>|\<close> 110) where
  \<open>lunion xs [] = xs\<close> |
  \<open>lunion xs (y # ys) = (if y |\<in>| xs then lunion xs ys else y # (lunion xs ys))\<close>

lemma lunion_simp[simp]: \<open>set (xs |\<union>| ys) = set xs \<union> set ys\<close> 
  by (induct ys) auto

primrec isset where
  \<open>isset [] = True\<close> |
  \<open>isset (x # xs) = (x |\<notin>| xs \<and> isset xs)\<close>

lemma isset_length: \<open>isset xs \<Longrightarrow> size xs = size (sorted_list_of_set (set xs))\<close>
  by (induct xs) simp_all
(*-------------------------*)


datatype trm
  = Var nat
  | Const nat
  | Fun nat \<open>trm list\<close>

datatype mat
  = Lit bool nat \<open>trm list\<close>
  | Mat \<open>(nat \<times> mat list) list\<close>

fun exi_clause where
  \<open>exi_clause P (Lit _ _ _) = False\<close> |
  \<open>exi_clause P (Mat []) = False\<close> |
  \<open>exi_clause P (Mat ((n,ms) # cs)) = 
  (P (n,ms) \<or> (\<exists> m \<in> set ms. exi_clause P m) \<or> exi_clause P (Mat cs))\<close>

definition \<open>exi_mat P m \<equiv> P m \<or> exi_clause (\<lambda> (_,ms). \<exists> m' \<in> set ms. P m') m\<close>

fun all_clause where
  \<open>all_clause P (Lit _ _ _) = True\<close> |
  \<open>all_clause P (Mat []) = True\<close> |
  \<open>all_clause P (Mat ((n,ms) # cs)) = 
  (P (n,ms) \<and> (\<forall> m \<in> set ms. all_clause P m) \<and> all_clause P (Mat cs))\<close>

definition \<open>all_mat P m \<equiv> P m \<and> all_clause (\<lambda> (_,ms). \<forall> m' \<in> set ms. P m') m\<close>

definition \<open>id_exists idty m \<equiv> exi_clause (\<lambda> (n,_). n = idty) m\<close>

fun ids_unique where
  \<open>ids_unique (Lit b n ts) = True\<close> |
  \<open>ids_unique (Mat []) = True\<close> |
  \<open>ids_unique (Mat ((n,ms) # cs)) = (
    (\<forall> m \<in> set ms. ids_unique m \<and> \<not>id_exists n m) \<and> 
    \<not>id_exists n (Mat cs) \<and> 
    ids_unique (Mat cs))\<close>

primrec siblings where
  \<open>siblings c1 c2 (Lit _ _ _) = False\<close> |
  \<open>siblings c1 c2 (Mat cs) = (member c1 cs \<and> member c2 cs)\<close>

abbreviation \<open>
  alpha_top_level cid l m \<equiv> (\<exists> c cid' c'. 
    cid \<noteq> cid' \<and> 
    siblings (cid,c) (cid',c') m \<and> 
    (\<exists> m' \<in> set c'. exi_mat (\<lambda> l'. l = l') m'))\<close>

definition \<open>
  alpha_related m cid l \<equiv> 
    exi_mat (alpha_top_level cid l) m\<close>

primrec union_many where
  \<open>union_many [] = {}\<close> |
  \<open>union_many (xs # ys) = xs \<union> (union_many ys)\<close>

primrec vars_term where 
  \<open>vars_term (Var i) = {i}\<close> |
  \<open>vars_term (Const i) = {}\<close> |
  \<open>vars_term (Fun i ts) = union_many (map vars_term ts)\<close>

primrec var_in_mat where
  \<open>var_in_mat v (Lit _ _ ts) = (\<exists> t \<in> set ts. v \<in> vars_term t)\<close> |
  \<open>var_in_mat v (Mat _) = False\<close>

abbreviation \<open>var_in_mats v ms \<equiv> (\<exists> m \<in> ms. exi_mat (var_in_mat v) m)\<close>

abbreviation \<open>var_in_clause v cid m \<close>

definition \<open>
  free_var v cid m \<equiv> 
    exi_mat (\<lambda> m'. \<exists> c. (cid,c) \<in> set m') m\<close>

primrec substitute where
\<open>substitute \<sigma> (Var i) = Var (\<sigma> i)\<close> |
\<open>substitute \<sigma> (Const i) = Const i\<close> |
\<open>substitute \<sigma> (Fun i ts) = Fun i (map (substitute \<sigma>) ts)\<close>

definition 
\<open>compliment \<sigma> pol pred trms pol' pred' trms' \<equiv>
  (pol \<longleftrightarrow> \<not>pol') \<and> pred = pred' \<and> (map (substitute \<sigma>) trms  = map (substitute \<sigma>) trms')\<close>

definition \<open>permutation xs ys \<equiv> length xs = length ys \<and> set xs \<inter> set ys = {}\<close>

inductive CC' (\<open>\<turnstile> _ _ _ _\<close> 0) where 
Axiom: \<open>\<turnstile> _ [] _ _\<close> |
Reduction: \<open>
  (\<turnstile> \<sigma> C M ((pol,pred,trms) # P)) \<Longrightarrow>
  compliment \<sigma> pol pred trms pol' pred' trms' \<Longrightarrow>
  (\<turnstile> \<sigma> ((Lit pol' pred' trms') # C) M ((pol,pred,trms) # P))\<close> |
Permutation: \<open>
  (\<turnstile> \<sigma> C M P) \<Longrightarrow>
  permutation C C' \<Longrightarrow> permutation P P' \<Longrightarrow>
  (\<turnstile> \<sigma> C' M P')\<close> 

(*
Extension: \<open>
  (\<turnstile> \<sigma> C M P) \<Longrightarrow>
  copy_clause \<delta> M C1 C2 \<Longrightarrow>
  (mat_replace C1 C2 (Mat M) (Mat M')) \<Longrightarrow>
  (\<turnstile> \<sigma> C3 M' (P |\<union>| \<lbrace>(pol,pred,trms)\<rbrace>)) \<Longrightarrow>
  b_clause (pol,pred,trms) C2 (_,C3) \<Longrightarrow>
  extension_clause M (P |\<union>| \<lbrace>(pol,pred,trms)\<rbrace>) C1 \<Longrightarrow>
  contains_mat_in_clause (Lit pol' pred' trms') C2 \<Longrightarrow>
  compliment \<sigma> pol pred trms pol' pred' trms' \<Longrightarrow>
  (\<turnstile> \<sigma> (C |\<union>| \<lbrace>Lit pol pred trms\<rbrace>) M P)\<close> |
Decomposition: \<open>
  (\<turnstile> \<sigma> (C |\<union>| C') M P) \<Longrightarrow>
  (_,C') |\<in>| M' \<Longrightarrow>
  (\<turnstile> \<sigma> (C |\<union>| \<lbrace>Mat M'\<rbrace>) M P)\<close>*)


function free_vars where
  \<open>free_vars M\<close>

function b_clause where
  \<open>b_clause pol pred trms \<lbrace>\<rbrace> = \<lbrace>\<rbrace>\<close> |
  \<open>b_clause pol pred trms (Insert (Lit pol' pred' trms') C) = (
    if pol = pol' \<and> pred = pred' \<and> trms = trms'
    then C
    else Insert (Lit pol' pred' trms') (b_clause pol pred trms C))\<close> |
  \<open>b_clause pol pred trms (Insert (Mat \<lbrace>\<rbrace>) C) = (Insert (Mat \<lbrace>\<rbrace>) C)\<close> |
  \<open>b_clause pol pred trms (Insert (Mat (Insert (Cls idC' C') Cs)) C) = (
    if mat_in_clause (Lit pol pred trms) (Cls idC' C')
    then (Insert (Mat (\<lbrace>(Cls idC' (b_clause pol pred trms C'))\<rbrace>)) C)
    else (Insert (Mat (Insert (Cls idC' C') Cs)) (b_clause pol pred trms C)))\<close> 
  by pat_completeness auto
termination
  apply (relation \<open>measure (\<lambda> (_, _, _, C). mat_elem_size (Cls 0 C))\<close>) 
  by simp_all (metis add.assoc ignore_id less_SucI less_add_Suc1)

inductive mat_replace where
\<open>\<not> contains_clause_in_mat C M \<Longrightarrow> mat_replace C C' (Mat M) (Mat M)\<close> |
\<open>mat_replace C C' (Lit pol pred trms) (Lit pol pred trms)\<close> |
\<open>C |\<in>| Cs \<Longrightarrow> mat_replace C C' (Mat Cs) (Mat (finsert C' (Cs |-| \<lbrace>C\<rbrace>)))\<close> |
\<open>
  contains_clause_in_mat C M \<Longrightarrow> 
  (Mat M) |\<in>| C'' \<Longrightarrow> (idC'',C'') |\<in>| Cs \<Longrightarrow> 
  mat_replace C C' (Mat M) M' \<Longrightarrow>
  mat_replace C C' 
    (Mat Cs) 
    (Mat (finsert (idC'',finsert M' (C'' |-| \<lbrace>Mat M\<rbrace>)) (Cs |-| \<lbrace>(idC'',C'')\<rbrace>)))\<close>

fun free_vars_trm where
  \<open>free_vars_trm (Var n) = \<lbrace>n\<rbrace>\<close> |
  \<open>free_vars_trm (Const n) = \<lbrace>n\<rbrace>\<close> |
  \<open>free_vars_trm (Fun n trms) = fold (\<lambda> t s. s |\<union>| free_vars_trm t) trms \<lbrace>\<rbrace>\<close>

definition \<open>free_vars_trms trms \<equiv> fold (\<lambda> t s. s |\<union>| free_vars_trm t) trms \<lbrace>\<rbrace>\<close>

abbreviation \<open>contains_var_in_lit_in_clause var pol pred trms C \<equiv>
  var |\<in>| free_vars_trms trms \<and> 
  contains_mat_in_clause (Lit pol pred trms) C\<close>

abbreviation \<open>contains_mat_in_mat M M' \<equiv> 
  (\<exists> C. contains_mat_in_clause (Mat M) C \<and> contains_clause_in_mat C M')\<close>

definition \<open>alpha_related M C pol pred trms \<equiv> 
  (\<exists> M' C1 C2. (contains_mat_in_mat M' M \<or> M' = M) \<and>
  C1 |\<in>| M' \<and> C2 |\<in>| M' \<and> C1 \<noteq> C2 \<and>
  (C = C1 \<or> contains_clause_in_clause C C1) \<and>
  contains_mat_in_clause (Lit pol pred trms) C2)\<close>

definition free_vars_clause where
  \<open>free_vars_clause M C \<equiv> 
  THE vars. \<forall> var. var |\<in>| vars \<longleftrightarrow> (
    \<exists> pol pred trms. 
    contains_var_in_lit_in_clause var pol pred trms C) \<and> 
    (\<forall> pol' pred' trms' C'. 
      contains_var_in_lit_in_clause var pol' pred' trms' C' \<longrightarrow>
      contains_clause_in_mat C' M \<longrightarrow>
        (contains_clause_in_clause C' C \<or>
        C' = C \<or>
        alpha_related M C pol' pred' trms'))\<close>

definition \<open>vars_in_mat M \<equiv> THE nset. \<forall> var. var |\<in>| nset \<longleftrightarrow> (\<exists> pol pred trms C idC.
  var |\<in>| free_vars_trms trms \<and> Lit pol pred trms |\<in>| C \<and> contains_clause_in_mat (idC,C) M)\<close>

primrec copy_term where
\<open>copy_term \<delta> (Var i) = Var (\<delta> i)\<close> |
\<open>copy_term \<delta> (Const i) = Const i\<close> |
\<open>copy_term \<delta> (Fun i trms) = Fun i (map (copy_term \<delta>) trms)\<close>

inductive copy_clause_elem where
\<open>copy_clause_elem \<delta> (Lit pol pred trms) (Lit pol pred (map (copy_term \<delta>) trms))\<close> |
\<open>\<forall> C. C |\<in>| M \<longrightarrow> 
  (\<exists> C'. C' |\<in>| M' \<and> C = (idC,C1) \<and> C' = (idC',C2) \<and> idC = idC' \<and>
    (\<forall> cm. cm |\<in>| C1 \<longrightarrow>
    (\<exists> cm'. cm' |\<in>| C2 \<and> copy_clause_elem \<delta> cm cm'
  ))) \<Longrightarrow>
\<forall> C'. C' |\<in>| M' \<longrightarrow> 
 (\<exists> C. C |\<in>| M \<and> C = (idC,C1) \<and> C' = (idC',C2) \<and> idC = idC' \<and>
   (\<forall> cm'. cm' |\<in>| C2 \<longrightarrow>
     (\<exists> cm. cm |\<in>| C1 \<and> copy_clause_elem \<delta> cm cm'
  ))) \<Longrightarrow> 
copy_clause_elem \<delta> (Mat M) (Mat M')\<close>

abbreviation \<open>copy_function \<delta> M C \<equiv> \<forall> var. 
  var |\<in>| vars_in_mat \<lbrace>C\<rbrace> \<longrightarrow> 
  (var |\<in>| free_vars_clause M C \<longrightarrow>
  \<delta> var |\<notin>| vars_in_mat M) \<and>
  (var |\<notin>| free_vars_clause M C \<longrightarrow>
  \<delta> var = var)\<close>

definition \<open>copy_clause \<delta> M C1 C2 \<equiv> 
  copy_function \<delta> M C1 \<and>
  copy_clause_elem \<delta> (Mat \<lbrace>C1\<rbrace>) (Mat \<lbrace>C2\<rbrace>)\<close>

fun snd_fold where
  \<open>snd_fold f (fst',snd') = (fst', fold f snd')\<close>

definition \<open>parent_clause M C \<equiv> THE (idC',C').
  contains_clause_in_mat (idC',C') M \<and> (\<exists> M'. (Mat M') |\<in>| C' \<and> C |\<in>| M')\<close>

definition \<open>extension_clause M P C \<equiv> 
  contains_clause_in_mat C M \<and>
  ((\<exists> pol pred trms. 
    contains_mat_in_clause (Lit pol pred trms) C \<and>
    (pol,pred,trms) |\<in>| P) \<or>
  ((\<forall> pol pred trms C'. 
    (pol,pred,trms) |\<in>| P \<longrightarrow>
    contains_mat_in_clause (Lit pol pred trms) C' \<longrightarrow>
    C' |\<in>| M \<longrightarrow>
    alpha_related M C pol pred trms) \<and>
  (C |\<notin>| M \<longrightarrow> (\<exists> pol pred trms. 
    (pol,pred,trms) |\<in>| P \<and>
    contains_mat_in_clause (Lit pol pred trms) (parent_clause M C)))))\<close>

inductive CC' (\<open>\<turnstile> _ _ _ _\<close> 0) where 
Axiom: \<open>\<turnstile> _ \<lbrace>\<rbrace> _ _\<close> |
Reduction: \<open>
  (\<turnstile> \<sigma> C M (finsert (pol,pred,trms) P)) \<Longrightarrow>
  compliment \<sigma> pol pred trms pol' pred' trms' \<Longrightarrow>
  (\<turnstile> \<sigma> (finsert (Lit pol pred trms) C) M (finsert (pol,pred,trms) P))\<close> |
Extension: \<open>
  (\<turnstile> \<sigma> C M P) \<Longrightarrow>
  copy_clause \<delta> M C1 C2 \<Longrightarrow>
  (mat_replace C1 C2 (Mat M) (Mat M')) \<Longrightarrow>
  (\<turnstile> \<sigma> C3 M' (P |\<union>| \<lbrace>(pol,pred,trms)\<rbrace>)) \<Longrightarrow>
  b_clause (pol,pred,trms) C2 (_,C3) \<Longrightarrow>
  extension_clause M (P |\<union>| \<lbrace>(pol,pred,trms)\<rbrace>) C1 \<Longrightarrow>
  contains_mat_in_clause (Lit pol' pred' trms') C2 \<Longrightarrow>
  compliment \<sigma> pol pred trms pol' pred' trms' \<Longrightarrow>
  (\<turnstile> \<sigma> (C |\<union>| \<lbrace>Lit pol pred trms\<rbrace>) M P)\<close> |
Decomposition: \<open>
  (\<turnstile> \<sigma> (C |\<union>| C') M P) \<Longrightarrow>
  (_,C') |\<in>| M' \<Longrightarrow>
  (\<turnstile> \<sigma> (C |\<union>| \<lbrace>Mat M'\<rbrace>) M P)\<close>

inductive CC where
Start:
\<open>\<turnstile> \<sigma> C2 M \<lbrace>\<rbrace> \<Longrightarrow> copy_clause \<delta> M C1 (_,C2) \<Longrightarrow> contains_clause_in_mat C1 M \<Longrightarrow>
  CC M\<close>

(*Examples*)
lemma \<open>CC \<lbrace>(0,\<lbrace>Lit True 1 []\<rbrace>),(1,\<lbrace>Lit False 1 []\<rbrace>)\<rbrace>\<close>
proof-
  let ?f = \<open>\<lambda> i. i\<close>
  let ?C0 = \<open>(0,\<lbrace>Lit True 1 []\<rbrace>)\<close>
  let ?C1 = \<open>(1,\<lbrace>Lit False 1 []\<rbrace>)\<close>
  let ?M = \<open>\<lbrace>?C0,?C1\<rbrace>\<close>
  have copy_fun: \<open>copy_function ?f ?M ?C0\<close> 
  proof-
    have \<open>vars_in_mat \<lbrace>?C0\<rbrace> = \<lbrace>\<rbrace>\<close>
  have copy1: \<open>copy_clause ?f ?M (0,\<lbrace>Lit True 1 []\<rbrace>) (0,\<lbrace>Lit True 1 []\<rbrace>)\<close> 
  from Start have ?thesis if 
    \<open>\<turnstile> (\<lambda> i. i) \<lbrace>Lit True 1 []\<rbrace> \<lbrace>(0,\<lbrace>Lit True 1 []\<rbrace>),(1,\<lbrace>Lit False 1 []\<rbrace>)\<rbrace> \<lbrace>\<rbrace>\<close>
    using that 

end
