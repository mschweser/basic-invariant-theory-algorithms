using Oscar

# function to produce all exponents beta = (beta_1, ..., beta_n) with |beta| = d recursivly 
# input is number of indeterminantes n and degree d
# output is list of all exponent vectors
# input types: n::Int, d::Int
# output type: Vector{Vector{Int}}
function make_exponent_list(n::Int, d::Int)
    exponent_list = Vector{Vector{Int}}()
    beta = zeros(Int, n)
    # i is position in beta, remaining is remaining degree to distribute on exponent vector
    # function calls itself recursivly going through ever position i in exponent vector
    # and trying out all possible combinations of remaining degree position by position and safe every vector to exponent_list
    # when last position is reached
    function fill_list(i::Int, remaining::Int)
        if i == n # recursion ends when i == n 
            beta[i] = remaining # all remaining degree is put in last position of vector
            push!(exponent_list, copy(beta)) # save vector to list
            return
        end
        for p in 0:remaining 
            beta[i] = p
            fill_list(i + 1, remaining - p)
        end # fill vector 
    end
    fill_list(1, d)
    return exponent_list
end

# make a list with all monomials of total degree beta in ring R
# input is ring R and list of exponents beta
# input types: R::MPolyRing, beta::AbstractVector{<:Integer}
# output type: elem_type(R), which is a subtype of MPolyRingElem
function monomial_from_exponent(R::MPolyRing, beta::AbstractVector{<:Integer})
    m = one(R) # neutral element for multiplication
    for i in 1:ngens(R)
        m *= gen(R, i)^beta[i] # builds monomial by multiplication
    end
    return m
end

# make list with coefficients of monomials in polynomial f, going through all possible exponents
# of monomials of degree beta
# for every possible exponent vector the coefficient of the corresponding monomial in f is saved to a list
# nput types: f::MPolyRingElem,
#              exponent_list::AbstractVector{<:AbstractVector{<:Integer}}
# output type: vector of elements of the coefficient ring of parent(f)
function coefficient_vector(f::MPolyRingElem, exponent_list::AbstractVector{<:AbstractVector{<:Integer}})
    return [
        coeff(forget_grading(f), beta)
        for beta in exponent_list
    ]
end


# compute hilbertseries with oscar function hilbert_series_reduced(A)
# in this function input is convereted into input for oscar function
# where B=k[f_1, ..., f_m] is isomorphic to quotientring A = S/I
# with S = k[y_1,...,y_m], the map phi with phi(y_i) = f_i and I = ker(phi)
# input is generators = f_1, ..., f_m and polynomial ring T, t = polynomial_ring(QQ, :t) 
# and F = parent(molien) = QQ(t) is the fraction field where molien lives in
# needed for hilbert and molien series
# output is hilbert series H, quotientring A and induced homomorphisms
# input types: R::MPolyRing,
#              generators::AbstractVector{<:MPolyRingElem},
#              T::PolyRing, F::FracField
# output type: tuple (H, A, projection, bar_phi) where hilbert series H is an element of F
#              A is an MPolyQuoRing and projection : S -> A = S/I, p |-> [p] and bar_phi : A -> R, [y_i] |-> f_i are maps
#              for empty generators list the last three entries are nothing
function compute_hilbertseries(R::MPolyRing, generators::AbstractVector{<:MPolyRingElem}, T::PolyRing, F::FracField)
    if isempty(generators)
        return F(one(T)), nothing, nothing, nothing
    end # for B = k is H_B(t) = 1
    K = coefficient_ring(R)
    m = length(generators)
    weights = [
        total_degree(f) 
        for f in generators
    ] # deg(y_i) = deg(f_i)
    names = [
        Symbol("y", i)
        for i in 1:m
    ] # [:y1, ..., :ym]
    S, y = graded_polynomial_ring(K, names; weights = weights) # S = K[y_1,...,y_m]
    phi = hom(S, R, generators) # phi : S -> R, y_i |-> f_i
    I = kernel(phi) # ideal of realtions
    A, projection = quo(S, I) # A = S/I
    bar_phi = hom(A, R, generators) # bar_phi : A -> R, [y_i] |-> f_i
    p, q = hilbert_series_reduced(A) # use oscar function, input is quotient ring, output is rational function p/q
    # output can be of type ZZPolyRingElem or of type Fac{ZZPolyRingElem} (if I = <0>)
    # for I = (0) the output is p, q with typeof(q) = FacElem{ZZPolyRingElem, ZZPolyRing}
    # then the function change_base_ring does not work
    if q isa typeof(p) # if I != (0) then q is already a ZZPolyRingElem
        q_poly = q
    else # if I = (0) then the type of q is FacElem{ZZPolyRingElem, ZZPolyRing}
        q_poly = evaluate(q) # evaluate(a::Fac{T}) -> T
    end
    # hilbert series has to be in same fraction field as molien to compute difference = molien - hilbert
    H = F(change_base_ring(QQ, p; parent=T)) / F(change_base_ring(QQ, q_poly; parent=T)) 
    return H, A, projection, bar_phi
end
