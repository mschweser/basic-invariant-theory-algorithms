# input F = [f_1, ..., f_m] generators of invariant ring R^G = k[f_1, ..., f_m]
# and polynomial f in R = k[x_1, ..., x_n]
# output is (belongs, g) with `belongs` is "true" if f is in R^G and "false" if not
# and if f is in R^G then g is polynomial in k[y_1, ..., y_m] with f = g(f_1, ..., f_m)

# use Lemma 3.2.13:
# < is monomial order where all polynomials involving x_1, ..., x_n are 
# greater than y_1, ..., y_m in k[x_1, ..., x_n, y_1, ..., y_m]
# GG is Groebnerbasis of <f_1 - y_1, ..., f_m - y_m> 
# f in k[f_1, ..., f_m] <=> g in k[y_1, ..., y_m] with g = f^GG
# if f in k[f_1, ..., f_m] then f = g(f_1, ..., f_m)

# algorithm
# 1. compute Groebnerbasis GG for the ideal <f_1 - y_1, ..., f_m - y_m>
# 2. compute g = f^GG 
# 3. decide wether g is in k[y_1, ..., y_m]
# 4. if 3 is true, write f as g(f_1, ..., f_m)


using Oscar

# function for f in k
# check if all generators are elements of k (true if list is empty)
function membership_representation(F::AbstractVector, f::RingElem)
    parent(f) isa Field || 
        error("The input f must be a field or polynomial ring element over a field.")
    all(fi -> fi isa RingElem && parent(fi) === parent(f), F) ||
        error("All generators and f must belong to the same field.")
    return true, f
end

# function for polynomial f
function membership_representation(F::AbstractVector, f::Union{PolyRingElem, MPolyRingElem})

    R = parent(f)
    K = base_ring(R)
    K isa Field || error("The coefficient ring must be a field.")

    # if F is empty, then k[F] = k 
    if isempty(F)
        # if f is constant, then f is in k
        if is_constant(f)
            return true, constant_coefficient(f)
        end 
        # else f is not constant, then f is not in k[F] = k
        return false, nothing 
    end

    # check if all generators f_1, ..., f_m are elements in R = k[x_1, ..., x_n]
    all(fi -> fi isa Union{PolyRingElem, MPolyRingElem} && parent(fi) === R, F) ||
        error("All generators and f must belong to the same polynomial ring.")

    # construct ideal I = <f_1 - y_1, ..., f_m - y_m> in ring S = k[x_1, ..., x_n, y_1, ..., y_m]
    # use lex ordering, then x_1 > ... > x_n > y_1 > ... > y_m
    n = ngens(R)
    m = length(F)
    names = vcat([Symbol("x_$i") for i in 1:n], [Symbol("y_$i") for i in 1:m])
    # S = k[x_1, ..., x_n, y_1, ..., y_m]
    S, z = polynomial_ring(K, names; internal_ordering = :lex) 
    x = z[1:n] # x_1, ..., x_n in S
    y = z[n+1:n+m] # y_1, ..., y_m in S
    if f isa PolyRingElem # f is univariate, method takes image of one generator
        phi = hom(R, S, x[1])
    else # f is multivariate, method takes vector of all generator images
        phi = hom(R, S, x) 
    end
    F_S = [phi(fi) for fi in F] # needed to construct ideal I
    f_S = phi(f) # image of f in I
    I = ideal(S, [F_S[i] - y[i] for i in 1:m]) # I = <f_1 - y_1, ..., f_m - y_m>
    
    # compute groebner basis GG and g is remainder of f on division by GG
    # f in k[f_1, ..., f_m] <=> g in k[y_1, ..., y_m] with g = f^GG
    GG = groebner_basis(I)
    g = reduce(f_S, GG) # g = f^GG remainder of f on division by GG

    # g in k[y_1, ..., y_m] if the exponents of x_1, ..., x_n are 0 in every monomial
    for e in AbstractAlgebra.exponent_vectors(g)
        if any(e[i] != 0 for i in 1:n) # any exponent of x_1, ..., x_n is not 0
            return false, nothing # g is not in k[y_1, ..., y_m], f is not in k[f_1, ..., f_m]
        end
    end
    # now g lies in k[y_1, ..., y_m]
    
    # construct T = k[y_1, ..., y_m] and map g into it, g |-> h
    # then f = h(f_1, ..., f_m)
    T, Y = polynomial_ring(K, [Symbol("y_$i") for i in 1:m])
    # define homomorphims 
    # psi : S = k[x_1, ..., x_n, y_1, ..., y_m] -> T = k[Y_1, ..., Y_m]
    # x_i |-> 0, y_i |-> Y_i
    psi = hom(S, T, vcat(fill(zero(T), n), Y))
    h = psi(g)
    # now g |-> h lies in k[y_1, ..., y_m] and f is h(f_1, ..., f_m)
    return true, h
end
