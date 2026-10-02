#set par(justify: true)
#show link: underline
#import "@preview/physica:0.9.7"
#set math.equation(numbering: "(1)", number-align: bottom)
#let hfrac(a, b) = math.frac(a, b, style: "horizontal")
#let sfrac(a, b) = math.frac(a, b, style: "skewed")

// Theorem-like environments.
// Each kind is a distinct figure kind, so each gets its own independent counter.
// `emph` controls whether the statement is italicized.
#let env-kinds = (
  definition: (supplement: [Definition], emph: false),
  lemma: (supplement: [Lemma], emph: true),
  proposition: (supplement: [Proposition], emph: true),
  theorem: (supplement: [Theorem], emph: true),
  corollary: (supplement: [Corollary], emph: true),
  remark: (supplement: [Remark], emph: false),
)

// Proof display: "footnote" or "inline". Applies to all subsequent blocks:
//   #proof-mode.update("inline")
// Individual blocks can override this with `proof-style: "inline"` (or "footnote").
#let proof-mode = state("proof-mode", "footnote")
#let todo = text(fill: red)[*TODO*]

#let theorem-envs(doc) = {
  show figure: it => if type(it.kind) == str and it.kind in env-kinds {
    set align(start)
    rect(width: 100%, it.caption)
  } else { it }
  show figure.caption: it => if type(it.kind) == str and it.kind in env-kinds [
    #set text(size: 10pt)
    *#it.supplement #context it.counter.display(it.numbering).* #it.body
  ] else { it }
  doc
}

#let env(kind) = (statement, title: none, proof: none, proof-style: auto) => figure(
  kind: kind,
  supplement: env-kinds.at(kind).supplement,
  caption: context {
    set math.equation(numbering: none)
    let body = if env-kinds.at(kind).emph { emph(statement) } else { statement }
    let mode = if proof-style == auto { proof-mode.get() } else { proof-style }
    if title != none [_*#title.*_]
    if proof != none and mode == "footnote" { footnote[_Proof:_ #proof] }
    [ ]
    body
    if proof != none and mode == "inline" [
      #parbreak()
      _Proof._ #proof #h(1fr) $square$
    ]
  },
  [],
)

#let definition = env("definition")
#let lemma = env("lemma")
#let proposition = env("proposition")
#let theorem = env("theorem")
#let corollary = env("corollary")
#let remark = env("remark")

#show: theorem-envs


= Generalized Vibrational Analysis


// ============================================================================
== Part I: Linear Algebra on a Metric Space
// ============================================================================

_Goal:_ establish vectors, covectors, the metric, and projection operators with no reference to coordinates or physics.
Raising and lowering indices arise naturally as the way the metric turns vectors into covectors.

=== A single space

#definition(
  [
    Let $V$ be an $n$-dimensional real vector space with basis ${bold(e)_i}$.
    Every vector $bold(v) in V$ has components $v^i$ with $bold(v) = v^i bold(e)_i$,
    where repeated upper and lower indices are summed.
    A _covector_ is a linear map $bold(alpha): V -> RR$,
    and the covectors form the _dual space_ $V^*$.
    The components of a covector are $alpha_i equiv bold(alpha)(bold(e)_i)$,
    so that $bold(alpha)(bold(v)) = alpha_i v^i$.
  ],
  title: "Vectors and covectors",
) <def:vectors-and-covectors>

#definition(
  [
    A _metric_ on $V$ is a symmetric, positive-definite bilinear form $physica.iprod(dot, dot): V times V -> RR$.
    Its components are $G_(i j) equiv physica.iprod(bold(e)_i, bold(e)_j) = G_(j i)$,
    so that
    $
    physica.iprod(bold(v), bold(w)) = G_(i j) v^i w^j.
    $
  ],
  title: "Metric",
) <def:metric>

#definition(
  [
    The _lowering_ (flat) of a vector $bold(v)$ is the covector
    $bold(v)^flat equiv physica.iprod(bold(v), dot)$,
    i.e. $bold(v)^flat (bold(w)) = physica.iprod(bold(v), bold(w))$.
    Its components are written $v_i equiv (bold(v)^flat)_i$.
  ],
  title: "Lowering",
) <def:lowering>

#proposition(
  [
    $
    v_i = G_(i j) v^j
    quad quad
    physica.iprod(bold(v), bold(w)) = v_i w^i
    $
    The inner product is the contraction of a vector with the lowered form of the other.
  ],
  title: "Lowering in components",
  proof: todo,
) <prop:lowering-in-components>

#proposition(
  [
    The map $flat: V -> V^*$ is a linear bijection.
  ],
  title: "Lowering is invertible",
  proof: todo,
) <prop:lowering-is-invertible>

#definition(
  [
    The _raising_ (sharp) map $sharp: V^* -> V$ is the inverse of $flat$:
    $bold(alpha)^sharp$ is the unique vector with $(bold(alpha)^sharp)^flat = bold(alpha)$.
    Its components are written $alpha^i equiv (bold(alpha)^sharp)^i$,
    and the _contravariant metric_ $G^(i j)$ is defined as the component matrix of $sharp$:
    $
    alpha^i = G^(i j) alpha_j.
    $
  ],
  title: "Raising",
) <def:raising>

#lemma(
  [
    The co- and contravariant metrics are matrix inverses, and $G^(i j)$ is symmetric.
    $
    G^(i k) G_(k j) = G_(j k) G^(k i) = delta^i_j
    quad quad
    G^(i j) = G^(j i)
    $
  ],
  title: "Co- and contravariant metrics",
  proof: todo,
) <lem:co-and-contravariant-metrics>

#remark(
  [
    By construction, $(bold(v)^flat)^sharp = bold(v)$ and $(bold(alpha)^sharp)^flat = bold(alpha)$.
    The position of an index therefore tells us which object a component belongs to,
    and we write $v_i$ and $alpha^i$ freely.
  ],
  title: "Dual consistency",
) <rem:dual-consistency>

#definition(
  [
    The inner product of covectors is
    $physica.iprod(bold(alpha), bold(beta)) equiv physica.iprod(bold(alpha)^sharp, bold(beta)^sharp)$.
  ],
  title: "Covector inner product",
) <def:covector-inner-product>

#proposition(
  [
    $
    physica.iprod(bold(alpha), bold(beta)) = G^(i j) alpha_i beta_j = alpha_i beta^i
    quad quad
    physica.iprod(bold(v)^flat, bold(w)^flat) = physica.iprod(bold(v), bold(w))
    $
  ],
  title: "Covector inner product in components",
  proof: todo,
) <prop:covector-inner-product-in-components>

#definition(
  [
    An _orthogonal projector_ is a linear map $bold(P): V -> V$,
    with components $(bold(P) bold(v))^i = P^i_j v^j$,
    that is idempotent and self-adjoint:
    $
    bold(P)^2 = bold(P)
    quad quad
    physica.iprod(bold(P) bold(v), bold(w)) = physica.iprod(bold(v), bold(P) bold(w)).
    $
    Its _complement_ is $bold(Q) = bold(1) - bold(P)$.
  ],
  title: "Orthogonal projector",
) <def:orthogonal-projector>

#theorem(
  [
    For $bold(v) != bold(0)$, the orthogonal projector onto $"span"{bold(v)}$ is
    $
    bold(P)_bold(v) = frac(bold(v) times.o bold(v)^flat, physica.iprod(bold(v), bold(v)))
    quad quad
    (bold(P)_bold(v))^i_j = frac(v^i v_j, physica.iprod(bold(v), bold(v)))
    quad quad
    bold(P)_bold(v) bold(w) = bold(v) frac(physica.iprod(bold(v), bold(w)), physica.iprod(bold(v), bold(v))),
    $
    and $bold(Q)_bold(v) = bold(1) - bold(P)_bold(v)$ is the orthogonal projector onto the orthogonal complement of $bold(v)$.
  ],
  title: "Projection onto a vector",
  proof: todo,
) <thm:projection-onto-a-vector>

#corollary(
  [
    An orthogonal projector $bold(P)$ acts on covectors from the right,
    $(bold(alpha) bold(P))_j equiv alpha_i P^i_j$
    (i.e. $bold(alpha) bold(P) = bold(alpha) compose bold(P)$),
    and this is an orthogonal projector on $V^*$ with respect to the covector inner product,
    satisfying $(bold(P) bold(v))^flat = bold(v)^flat bold(P)$.
    In particular, for $bold(alpha) != bold(0)$, the projector onto $"span"{bold(alpha)}$ is
    $
    (bold(P)_bold(alpha))^i_j = frac(alpha^i alpha_j, physica.iprod(bold(alpha), bold(alpha)))
    quad quad
    bold(beta) bold(P)_bold(alpha) = bold(alpha) frac(physica.iprod(bold(alpha), bold(beta)), physica.iprod(bold(alpha), bold(alpha))).
    $
  ],
  title: "Projection of covectors",
  proof: todo,
) <cor:projection-of-covectors>

#definition(
  [
    The projection of a bilinear form $H_(i j)$ by an orthogonal projector $bold(P)$ is
    $H(bold(P) bold(v), bold(P) bold(w))$, with components
    $
    (H^bold(P))_(i j) equiv P^k_i H_(k l) P^l_j.
    $
  ],
  title: "Projection of a bilinear form",
) <def:projection-of-a-bilinear-form>


=== Linear maps between two spaces

From here on, Greek indices $mu, nu, rho, sigma$ refer to a space $V$ of dimension $n$
and Latin indices $i, j, k, l$ refer to a space $W$ of dimension $m <= n$.

#definition(
  [
    A linear map $bold(L): V -> W$ has components $(bold(L) bold(v))^i = L^i_mu v^mu$.
    Its _pullback_ (transpose) $bold(L)^*: W^* -> V^*$ is
    $bold(L)^* bold(beta) equiv bold(beta) compose bold(L)$,
    with components $(bold(L)^* bold(beta))_mu = beta_i L^i_mu$.
  ],
  title: "Linear map and pullback",
) <def:linear-map-and-pullback>

#proposition(
  [
    If $bold(L)$ is surjective, then $bold(L)^*$ is injective.
  ],
  title: "Pullback of a surjection is injective",
  proof: todo,
) <prop:pullback-injective>

#definition(
  [
    Given a metric on $V$ and a surjective $bold(L): V -> W$,
    the _induced_ covector inner product on $W^*$ is
    $
    physica.iprod(bold(beta), bold(gamma))_W equiv physica.iprod(bold(L)^* bold(beta), bold(L)^* bold(gamma))_V.
    $
    The induced metric on $W$ is the one whose raising and lowering reproduce this covector inner product.
  ],
  title: "Induced metric",
) <def:induced-metric>

#proposition(
  [
    The induced contravariant metric
    $
    G^(i j) = L^i_mu L^j_nu G^(mu nu)
    $
    is symmetric and positive-definite.
    Its inverse $G_(i j)$ is therefore the induced (covariant) metric on $W$.
  ],
  title: "Induced metric in components",
  proof: todo,
) <prop:induced-metric-in-components>

#theorem(
  [
    Let $bold(L): V -> W$ be surjective and equip $W$ with the induced metric.
    Define $bold(A): W -> V$ by $bold(A) equiv sharp_V compose bold(L)^* compose flat_W$, i.e.
    $
    A^mu_i = G^(mu nu) L^k_nu G_(k i).
    $
    Then:
    (a) $bold(L) bold(A) = bold(1)_W$, i.e. $L^i_mu A^mu_j = delta^i_j$;
    (b) $bold(A) bold(L)$ is the orthogonal projector on $V$ onto $(ker bold(L))^perp$;
    (c) $bold(A) bold(w)$ is the unique vector of minimum norm with $bold(L) bold(v) = bold(w)$;
    (d) $physica.iprod(bold(A) bold(w), bold(A) bold(w)') _V = physica.iprod(bold(w), bold(w)')_W$.
  ],
  title: "Minimum-norm lift",
  proof: todo,
) <thm:minimum-norm-lift>

#remark(
  [
    $bold(A)$ is simply $bold(L)$ with both of its indices moved by the metrics.
    When $m = n$, $bold(A) = bold(L)^(-1)$ and $bold(A) bold(L) = bold(1)_V$.
  ],
  title: "Interpretation of the lift",
) <rem:interpretation-of-the-lift>


// ============================================================================
#pagebreak()
== Part II: Coordinates and Derivatives
// ============================================================================

_Goal:_ show that coordinate displacements are vectors and derivatives are covectors,
so that the machinery of Part I applies to them.

#definition(
  [
    Let $q^mu$ be coordinates on a neighborhood of a reference point in configuration space.
    Infinitesimal displacements $dif bold(q)$, with components $dif q^mu$, are vectors.
    For a smooth function $f$, the differential
    $dif f (dif bold(q)) = physica.pdv(f, q^mu) dif q^mu$
    is linear in $dif bold(q)$,
    so $dif f$ is a covector with components $physica.pdv(f, q^mu)$.
  ],
  title: "Displacements and differentials",
) <def:displacements-and-differentials>

#definition(
  [
    A second set of $m <= n$ coordinates $q^i = q^i (q^mu)$ has _Jacobian_ and _second derivative_
    $
    B^i_mu equiv physica.pdv(q^i, q^mu)
    quad quad
    C^i_(mu nu) equiv physica.pdv(q^i, q^mu, q^nu) = C^i_(nu mu).
    $
    We assume $B^i_mu$ has full row rank at the reference point, so that $bold(B)$ is surjective.
  ],
  title: "Coordinate map",
) <def:coordinate-map>

#proposition(
  [
    $
    dif q^i = B^i_mu dif q^mu
    $
  ],
  title: "Displacements push forward",
  proof: todo,
) <prop:displacements-push-forward>

#proposition(
  [
    If $f$ depends on $q^mu$ only through $q^i$, then
    $
    physica.pdv(f, q^mu) = physica.pdv(f, q^i) B^i_mu,
    $
    i.e. $dif f$ in the $q^mu$ coordinates is the pullback $bold(B)^*$ of $dif f$ in the $q^i$ coordinates.
  ],
  title: "Gradients pull back",
  proof: todo,
) <prop:gradients-pull-back>

#remark(
  [
    When $m = n$ and $bold(B)$ is invertible, these become the classical contravariant and covariant transformation laws,
    and the contraction $physica.pdv(f, q^i) dif q^i = physica.pdv(f, q^mu) dif q^mu$ is invariant.
    When $m < n$, displacements can only be pushed forward and gradients can only be pulled back.
  ],
  title: "Transformation laws",
) <rem:transformation-laws>

#proposition(
  [
    If $f$ depends on $q^mu$ only through $q^i$, then
    $
    physica.pdv(f, q^mu, q^nu)
    = physica.pdv(f, q^i, q^j) B^i_mu B^j_nu
    + physica.pdv(f, q^k) C^k_(mu nu).
    $
    Second derivatives therefore transform as a bilinear form only when the map is linear ($C = 0$)
    or at a stationary point ($partial f slash partial q^k = 0$).
  ],
  title: "Second derivatives",
  proof: todo,
) <prop:second-derivatives>


// ============================================================================
#pagebreak()
== Part III: The Physical Model
// ============================================================================

_Goal:_ identify the kinetic energy as the metric, and apply Part I to Cartesian, mass-weighted Cartesian, and internal coordinates.

#definition(
  [
    For $N$ atoms with Cartesian coordinates $x^mu$ ($mu = 1, dots, 3N$),
    let $m_((mu))$ denote the mass of the atom to which coordinate $mu$ belongs.
    Cartesian displacements from a reference geometry are $q^mu = x^mu - x^mu_0$.
    The _kinetic-energy metric_ is
    $
    G_(mu nu) equiv m_((mu)) delta_(mu nu),
    $
    chosen so that $T = 1/2 physica.iprod(dot(bold(q)), dot(bold(q)))$.
  ],
  title: "Cartesian coordinates and kinetic-energy metric",
) <def:kinetic-energy-metric>

#proposition(
  [
    $
    G^(mu nu) = m_((mu))^(-1) delta^(mu nu)
    $
  ],
  title: "Contravariant Cartesian metric",
  proof: todo,
) <prop:contravariant-cartesian-metric>

#definition(
  [
    The mass-weighted Cartesian displacements are $tilde(q)^mu equiv m_((mu))^(1/2) q^mu$.
    Mass-weighted quantities are marked with a tilde.
  ],
  title: "Mass-weighted coordinates",
) <def:mass-weighted-coordinates>

#proposition(
  [
    $
    tilde(G)_(mu nu) = delta_(mu nu)
    quad quad
    tilde(G)^(mu nu) = delta^(mu nu)
    $
  ],
  title: "Mass-weighted metric",
  proof: todo,
) <prop:mass-weighted-metric>

#definition(
  [
    Internal coordinates $q^i$ ($i = 1, dots, M$, with $M = 3N - 6$, or $3N - 5$ for linear molecules)
    are displacements of non-redundant functions of the geometry that are invariant to overall translation and rotation.
    Their mass-weighted Jacobian (B-matrix) and its derivative (C-tensor) are
    $
    tilde(B)^i_mu equiv physica.pdv(q^i, tilde(q)^mu)
    quad quad
    tilde(C)^i_(mu nu) equiv physica.pdv(q^i, tilde(q)^mu, tilde(q)^nu),
    $
    and $tilde(B)^i_mu$ has full row rank at the reference geometry.
    Index-free internal-coordinate objects are marked with a prime, e.g. $bold(v)'$.
  ],
  title: "Internal coordinates",
) <def:internal-coordinates>

#theorem(
  [
    The metric induced on internal coordinates by $tilde(bold(B))$ has contravariant components
    $
    G^(i j) = delta^(mu nu) tilde(B)^i_mu tilde(B)^j_nu = sum_mu m_((mu))^(-1) B^i_mu B^j_mu,
    $
    where $B^i_mu = partial q^i slash partial q^mu$.
    The covariant internal-coordinate metric $G_(i j)$ is its inverse.
  ],
  title: "Wilson G-matrix",
  proof: todo,
) <thm:wilson-g-matrix>

#corollary(
  [
    The A-matrix
    $
    tilde(A)^mu_i equiv delta^(mu nu) tilde(B)^k_nu G_(k i)
    $
    satisfies $tilde(B)^i_mu tilde(A)^mu_j = delta^i_j$,
    and $tilde(A)^mu_i tilde(B)^i_nu$ is the orthogonal projector onto the vibrational subspace $(ker tilde(bold(B)))^perp$,
    where $ker tilde(bold(B))$ is spanned by infinitesimal translations and rotations.
  ],
  title: "A-matrix",
  proof: todo,
) <cor:a-matrix>

#proposition(
  [
    For Cartesian velocities orthogonal to $ker tilde(bold(B))$
    (no infinitesimal overall translation or rotation, i.e. the linearized Eckart conditions),
    $
    T = 1/2 G_(i j) dot(q)^i dot(q)^j.
    $
  ],
  title: "Kinetic energy in internal coordinates",
  proof: todo,
) <prop:kinetic-energy-in-internals>


// ============================================================================
#pagebreak()
== Part IV: Vibrational Analysis
// ============================================================================

_Goal:_ transform the gradient and Hessian into internal coordinates, set up the GF eigenproblem,
and project the gradient direction out of the Hessian.

#definition(
  [
    The gradient and Hessian in each coordinate system are defined by the Taylor expansion of the potential energy about the reference geometry:
    $
    V &= V_0 + g_mu q^mu + 1/2 H_(mu nu) q^mu q^nu + cal(O)(bold(q)^3) \
    V &= V_0 + tilde(g)_mu tilde(q)^mu + 1/2 tilde(H)_(mu nu) tilde(q)^mu tilde(q)^nu + cal(O)(tilde(bold(q))^3) \
    V &= V_0 + g_i q^i + 1/2 H_(i j) q^i q^j + cal(O)(bold(q)'^3)
    $
  ],
  title: "Gradient and Hessian",
) <def:gradient-and-hessian>

#proposition(
  [
    $
    tilde(g)_mu = m_((mu))^(-1/2) g_mu
    quad quad
    tilde(H)_(mu nu) = m_((mu))^(-1/2) m_((nu))^(-1/2) H_(mu nu)
    $
  ],
  title: "Mass-weighted gradient and Hessian",
  proof: todo,
) <prop:mass-weighted-gradient-and-hessian>

#theorem(
  [
    $
    g_i = tilde(g)_mu tilde(A)^mu_i
    $
  ],
  title: "Internal-coordinate gradient",
  proof: todo,
) <thm:internal-gradient>

#theorem(
  [
    $
    H_(i j) = (tilde(H)_(mu nu) - g_k tilde(C)^k_(mu nu)) tilde(A)^mu_i tilde(A)^nu_j
    $
    The correction term arises because the map to internal coordinates is non-linear (@prop:second-derivatives).
  ],
  title: "Internal-coordinate Hessian",
  proof: todo,
) <thm:internal-hessian>

#definition(
  [
    The _GF matrix_ is the internal-coordinate Hessian with its first index raised,
    $
    (bold(G F))^i_j equiv G^(i k) H_(k j),
    $
    a linear map on internal-coordinate displacements.
    Its eigenvalues are the squared harmonic frequencies $omega^2$.
  ],
  title: "GF matrix",
) <def:gf-matrix>

#proposition(
  [
    Let $tilde(P)^mu_nu = tilde(A)^mu_i tilde(B)^i_nu$.
    The eigenvalues of $G^(i k) H_(k j)$ are the eigenvalues of
    $tilde(P)^rho_mu (tilde(H)_(rho sigma) - g_k tilde(C)^k_(rho sigma)) tilde(P)^sigma_nu$
    restricted to the vibrational subspace.
    At a stationary point, these are the eigenvalues of the projected mass-weighted Hessian.
  ],
  title: "GF and mass-weighted Cartesian eigenvalues",
  proof: todo,
) <prop:gf-and-cartesian-eigenvalues>

#definition(
  [
    For $g_i != 0$, with $g^i = G^(i j) g_j$ and $physica.iprod(bold(g)', bold(g)') = G^(i j) g_i g_j$,
    the gradient-direction projector and its complement are
    $
    (bold(P)_bold(g))^i_j = frac(g^i g_j, physica.iprod(bold(g)', bold(g)'))
    quad quad
    bold(Q)_bold(g) = bold(1) - bold(P)_bold(g).
    $
  ],
  title: "Gradient-direction projector",
) <def:gradient-direction-projector>

#theorem(
  [
    The projected Hessian
    $
    H^bold(Q)_(i j) = (Q_bold(g))^k_i H_(k l) (Q_bold(g))^l_j
    $
    gives a GF matrix $G^(i k) H^bold(Q)_(k j)$ with eigenvector $g^i$ of eigenvalue $0$.
    Every eigenvector $v^i$ with non-zero eigenvalue satisfies $g_i v^i = 0$,
    and these $M - 1$ eigenvalues are the generalized frequencies $omega^2$ for motion orthogonal to the gradient.
  ],
  title: "Projected Hessian",
  proof: todo,
) <thm:projected-hessian>

#remark(
  [
    _To investigate:_ the relation to Cartesian gradient projection (Miller, Handy, and Adams).
    Note that $tilde(A)^mu_i g^i = tilde(g)^mu$, so the gradient directions agree.
    By @prop:gf-and-cartesian-eigenvalues, however, the internal-coordinate result carries the curvature term $g_k tilde(C)^k_(mu nu)$,
    so projected frequencies away from stationary points depend on the choice of coordinates.
  ],
  title: "Comparison with Cartesian projection",
) <rem:comparison-with-cartesian-projection>
