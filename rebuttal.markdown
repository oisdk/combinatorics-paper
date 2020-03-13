We thank the reviewers for their time, and for their thorough and insightful
reviews.

# Review 1

> 2: (accept)
> The paper gives five definitions of finite types in CuTT and relates them.
> Three of the notions imply the type is discrete and three of the notions imply
> the type is ordered with two implying the type is both. If a type is both
> discrete and ordered, then the five notions are equivalent. Some closure
> properties are proven and these closure properties are used to prove that
> cardinal finite types form a category (in fact, a Pi-topos). Two notions of
> countably infinite types are considered, with one (countability) the
> propositional truncation of the other (split countability). Countable types
> are discrete. Countable types are closed under lists and the Kleene star.
> Omniscience and exhaustibility are briefly considered for finite types in
> Section 6. Discussion of using decidability results to automate some proofs is
> briefly considered in Section 7. The results are formalized in Cubical Agda
> and the sources are available online.

We think this summary is accurate, however we would like to emphasise the
topos-theoretic proofs in the paper as significant.
Constructive finiteness is an important area of study (see [1, etc]), and
expressing it formally as a Pi-pretopos was a clear next step (indeed, it was
called for specifically in [2]).
Furthermore, our formalisation is fully computer-checked, and a key
demonstration of two new theories: HoTT and CuTT.
The first sections of the paper rely specifically on HoTT (as [3] does), and the
proof automation section is possible as a direct consequence of a constructive
interpretation of the univalence axiom.

> The abstract says: "any totally ordered Kuratowski finite type is manifestly
> Bishop finite." Looking at Figure 1, as well as Theorem 1 and Lemmas 16, I
> think the statement in the abstract is wrong. Probably the authors either
> meant "any discrete totally ordered Kuratowski finite type is manifestly
> Bishop finite" (Theorem 1+Lemma 16) or "any totally ordered cardinal finite
> type is manifestly Bishop" (Theorem 1).

Our definition of "totally ordered" itself implies discreteness, which we now
see is unclear.
We will clarify the statement.

> The proof of Lemma 10 in the formalization depends on knowing that manifest
> enumerability implies Kuratowski finiteness. It might be worth saying this...

We will include the missing lemma.

> On Page 10 between Lemmas 13 and 14 is the text "This lemma is proven by
> truncating..." ... 
> I would prefer to see a brief explanation
> of how to prove Lemma 14 instead of (or in addition to) Lemma 13.

We will include an explanation of lemma 14.

> On Page 12, Equation (42) says "isProp" where I expect it to say "isSet." As
> it is, it would give a category of propositions instead of a category of sets.

This is correct: in the paper, isProp is a typo.
We use isSet in the formalisation.

> Section 4.3 is titled "The Pi-pretopos of Finite Sets." However, Theorem 3
> proves it's not just a Pi-pretopos but a Pi-topos. It might be better to
> retitle the section "The Pi-topos of Finite Sets."

This is indeed a mistake, however it is in the statement of Theorem 3.
Finite sets do not form a Pi-topos (in HoTT): we will fix the statement to say
they form a Pi-pretopos.

> Throughout the paper there are some proper nouns I think should be capitalized
> (e.g. "theorem 16" should be "Theorem 16"), but as long as the authors are
> consistent I wouldn't insist on this.

We will capitalize the proper nouns.

# Review 2

> Overall I think the paper is relatively well-written but too succint in some
> places. It is a walkthrough a formalization on finiteness in HoTT but doesn't
> really highlight interesting use of Cubical Type Theory or difficulty of
> interest in the formalization. The only potential case could have been section
> 6.2 but it's simply too short. I'm hence not sure it has its place at IJCAR.

We agree that section 6.2 is an important part of the paper: it was much larger
and more detailed in earlier drafts, and we will add back that detail to the
next version.
In particular we will describe in detail the relation between the library and
other similar libraries, and especially the importance of computational
univalence (which is indeed essential to the function of the library).

> You do not cite Realizability at Work: Separating Two Constructive Notions of
> Finiteness by Bezem et Al. (TYPES'16). It includes two other
> (classically-equivalent) notions of finiteness, it would be interesting to see
> how they would compare with the ones you study.

The two finiteness predicates in the mentioned paper are streamlessness and
noetherianness, which are explored in [1], which we do mention in the related
work section.
Although we would of course like to explore more notions of finiteness in a
longer paper, we chose to discuss only the notions of finiteness which were
necessary to our main results.

> p12: "we have proven the above... As far as we know this is the first
> formalization of either". That's unclear to me for Set's, isn't it precisely
> the case that it was proven in the HoTT book that hSets form a Pi-pretopos? Do
> you mean the original part is with this presentation of finite sets as C(A),
> or the fact that you replayed the HoTT book proof in CuTT?

We meant "formalization" in the sense of "computer-formalized".
In particular, the HoTT book describes its proofs as "unformalized" versions of
formal computer-assisted proofs (p10).

# Review 3

> * Several Lemmas and Theorems have no proof text in the paper. I would
>   appreciate at least one line for each lemma/theorem, *after the statement*,
>   containing either the idea of the proof or at least a citation to find it
>   written down somewhere.

We will include a short summary of each lemma, and an appendix of lemmas that
are too long to fit in the paper itself.

> This paper describes and establishes implications and equivalences between
> various notions of finiteness and countability in Cubical/Homotopy Type
> Theory. The paper is fairly well written and quite easy to understand, it goes
> together with formal code that passes cubical agda's checking, which is nice.
> The only problems to me is that the content of what is described in the paper
> seems straightforward with regard to what existed before (although fun to
> formalize) and that I did not witness direct applications of this work (e.g.
> to another formalization effort) nor the integration to a larger library with
> a purpose (e.g. refactoring it). If I am wrong, this must be mentioned in the
> paper, and in the absence of one of above ingredients, I consider the content
> a slightly too weak for publication.

We respectfully disagree with regards to the content: we feel that the core
contribution of our paper (the relation between finiteness predicates, and the
proof that cardinal finite sets form a Pi-pretopos in the setting of HoTT) is
significant and of impact in general.
See our response to Reviewer 1's summary.

As for applications, our work has two:

* We intend to integrate it with the cubical Agda library, itself a large
  formalisation of Homotopy Type Theory.
  This integration already exists "downstream" (we depend on the cubical Agda
  library and reuse many of its definitions): further integration is a matter of
  upstream merging.

* It is relatively standard to use finiteness formalisations as a basis for a
  proof search and proof automation library (see [4]).
  Our work aims to replace these libraries in Agda, with the following
  improvements allowed by CuTT:
  - It extends the domain of items to be searched over to include functions, a
    capability possible only with a constructive interpretation of the
    univalence axiom.
  - It provides a pure Agda interface for multiple dependent arguments.
  - The language of a Pi-pretopos provides a principled and simple interface for
    constructing proofs of finiteness: from these one can automatically derive
    equivalences to other finite types.
  We will expand on the uses of this proof search library in our rewrites.

[1]T. Coquand and A. Spiwack, “Constructively finite?,” in Contribuciones científicas en honor de Mirian Andrés Gómez, 2010, pp. 217–230.
[2]D. Frumin, H. Geuvers, L. Gondelman, and N. van der Weide, “Finite Sets in Homotopy Type Theory,” in Proceedings of the 7th ACM SIGPLAN International Conference on Certified Programs and Proofs, New York, NY, USA, 2018, pp. 201–214, doi: 10.1145/3167085.
[3]E. Rijke and B. Spitters, “Sets in homotopy type theory,” Math. Struct. Comp. Sci., vol. 25, no. 5, pp. 1172–1202, Jun. 2015, doi: 10.1017/S0960129514000553.
[4]D. Firsov and T. Uustalu, “Dependently typed programming with finite sets,” in Proceedings of the 11th ACM SIGPLAN Workshop on Generic Programming - WGP 2015, Vancouver, BC, Canada, 2015, pp. 33–44, doi: 10.1145/2808098.2808102.
