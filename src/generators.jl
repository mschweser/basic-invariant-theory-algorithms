# helpers includes the following functions:
# make_exponent_list(n::Int, d::Int)
# monomial_from_exponent(R::MPolyRing, beta::AbstractVector{<:Integer})
# coefficient_vector(f::MPolyRingElem, exponent_list::AbstractVector{<:AbstractVector{<:Integer}})
# compute_hilbertseries(R::MPolyRing, generators::AbstractVector{<:MPolyRingElem}, T::PolyRing, F::FracField)
include("helpers.jl")

using Oscar

# compute next degree with number of new linear independet invariants
# given the difference of the molien series - the hilbert series
# using theorem ???
# input is rational function difference = molien - hilbert
# output (d, c) as integers, where d is the next missing degree 
# and c is the number of missing invariants in that degree
# input type: AbstractAlgebra.Generic.FracFieldElem
# output type: Int, Int
function next_missing_degree(difference::AbstractAlgebra.Generic.FracFieldElem)
    p = numerator(difference)
    q = denominator(difference)
    # check that coefficient at t = 0 isnt 0
    # should not happen with difference = molien - hilbert
    iszero(coeff(q,0)) && error("The denominator vanishes at t = 0.") 
    d = 0 # start with degree = 0
    while iszero(coeff(p, d)) # next degree is the exponent of first nonzero term
        d += 1
    end 
    c = coeff(p, d) / coeff(q, 0)
    # check that number of missing invariants is a positive integer
    denominator(c) == 1 || error("The coefficient of lowest degree of Molien - Hilbert is not an integer.")
    c > 0 || error("The first coefficient of Molien - Hilbert is not positive.")
    return d, Int(numerator(c)) # numerator(c) = c_d is number of missing invariants in degree d
end

# compute basis for A_d = S/I using Oscar function monomial_basis
# function is needed to catch the case of empty generators
# input types: R::MPolyRing, generators::AbstractVector{<:MPolyRingElem},
#              A::Union{MPolyQuoRing, Nothing}, projection::Union{Map, Nothing},
#              bar_phi::Union{Map, Nothing}, d::Int
# output type: Vector{elem_type(R)}
function subalgebra_basis_of_degree(
    R::MPolyRing,
    generators::AbstractVector{<:MPolyRingElem},
    A::Union{MPolyQuoRing, Nothing},
    projection::Union{Map, Nothing}, # S -> A = S/I, p |-> [p]
    bar_phi::Union{Map, Nothing}, # A -> R, [y_i] |-> f_i
    d::Int
)
    if isempty(generators)
        return elem_type(R)[]
    end # for B = k is B_d = 0 for all d > 0
    basis_A_d = monomial_basis(A, d) # use Oscar function monomial_basis
    return [
        bar_phi(projection(m)) # S -> A -> R
        for m in basis_A_d
    ]
end

# compute new invariants of degree d using the reynolds operator
# end when number of independent invarinats is number_missing (known by molien series and hilbert series)
# input types: G::MatGroup, R::MPolyRing,
#              generators::AbstractVector{<:MPolyRingElem},
#              A::Union{MPolyQuoRing, Nothing}, projection::Union{Map, Nothing},
#              bar_phi::Union{Map, Nothing}, d::Int, number_missing::Int
# output type: Tuple{Vector{elem_type(R)}, Vector{elem_type(R)}}
function add_missing_invariants(
    G::MatGroup,
    R::MPolyRing,
    generators::AbstractVector{<:MPolyRingElem},
    A::Union{MPolyQuoRing, Nothing},
    projection::Union{Map, Nothing}, # S -> A = S/I, p |-> [p]
    bar_phi::Union{Map, Nothing}, # A -> R, [y_i] |-> f_i
    d::Int,
    number_missing::Int
)
    K = coefficient_ring(R)
    n = ngens(R)
    x = gens(R)
    exponent_list = make_exponent_list(n, d) # all possible exponents of given degree
    B_d_basis = subalgebra_basis_of_degree(R, generators, A, projection, bar_phi, d) # B = k[f_1, ... f_m] and B_d is homogenic part of B
    vectors = [
        coefficient_vector(f, exponent_list)
        for f in B_d_basis
    ] # all coefficient vectors on this list are linear independent
    added = elem_type(R)[] # list for new invariants
    # compute group action of every group element on the variables
    # (x_1, ..., x_n) |-> (x_1, ..., x_n) * A
    # output is vector [sum_i=1^n a_i1 * x_i, ..., sum_i=1^n a_in * x_i] = x * A for all A in G
    group_action_on_variables = [
        [
            sum((A[i, j] * x[i] for i in 1:n); init = zero(R))
            for j in 1:n
        ]
        for A in G
    ]

    # go through all possible exponents in given degree and form monomials
    # compute image of reynolds operator for every monomial to generate invariants
    # add linear independent invariants to generators list
    for beta in exponent_list
        m = monomial_from_exponent(R, beta)
        # reynolds_operator f = R_G (m)(x) := 1/|G| sum(A in G)(m (x * A))
        f = inv(K(order(G))) * sum((evaluate(m, images) for images in group_action_on_variables); init = zero(R))
        if iszero(f) # image of reynolds operator can be 0
            continue
        end
        # check if f linear independent via rank
        v = coefficient_vector(f, exponent_list)
        test_vectors = vcat(vectors, [v])
        M = matrix(
            K,
            length(test_vectors),
            length(exponent_list),
            reduce(vcat, test_vectors)
        ) # matrix for rank test
        if rank(M) > length(vectors) # then f is linear independent
            push!(vectors, v) # add coefficient vector of f to list of exponents for next rank test
            push!(added, f) # add f to list of generators in given degree
            if length(added) == number_missing # given by differnece = molien - hilbert
                break
            end
        end
    end
    length(added) == number_missing ||
        error("Could not find the required number of independent invariants in degree $d.")
    return vcat(generators, added), added # vcat(generators, added) is new generators list after given degree
end

# main function, implementing first part of sturmfels algorithm 2.2.5
# 1. compute molien series
# 2. compute hilbert series of subalgebra k[f_1, ..., f_m]
# 3. difference = molien - hilbert = c_d t^d + higher terms
# d is degree of next generator and c_d is number of linear independent generators of degree d
# 4. compute invariants using reynolds operator, test for linear independency
# terminates when molien = hilbert (the latest at noether bound |G])
# input R = k[x_1, ..., x_n], G <= Gl(n,k), debug boolian
# check if |G| < infty, char(k) = 0, degree(G) = number of variables of R
# and G and R must be over the same field k
# output f_1, ..., f_m with R^G = k[f_1, ..., f_m]

# function to catch case R = k is a field, then there are no variables and no positive-degree generators
# input types: K::Field, second argument::Nothing, debug::Bool
# output type: Vector{elem_type(K)} (empty vector)
function compute_generators(K::Field, ::Nothing; debug::Bool = true)
    return elem_type(K)[]
end

# input types: R::MPolyRing, G::MatGroup, debug::Bool
# output type: Vector{elem_type(R)}
function compute_generators(
    R::MPolyRing,
    G::MatGroup;
    debug::Bool = true
)
    # check input
    is_finite(G) || error("G must be finite.")
    degree(G) == ngens(R) || error("The degree of G must equal the number  of variables of R.")
    K = coefficient_ring(R)
    K isa Field || error("The coefficient ring must be a field.")
    base_ring(G) == K || error("G and R must be defined over the same field.")
    characteristic(K) == 0 || error("The coefficient field must have characteristic zero.")
    original_R = R
    # Oscar function invariant_ring needs graded ring as input
    if !(R isa MPolyDecRing)
        R, _ = grade(R)
    end
    # 1. compute molien series (using Oscar function)
    # use Oscar function to compute molien series, as it is not the goal
    # of this algorithm to show the mathematics behind computing moliens series
    IR = invariant_ring(R, G) # Oscar function does not compute generators, but IR is needed as input for computing molien series
    T, t = polynomial_ring(QQ, :t) # T = QQ[t], ring for denominator and numerator of molien series
    molien = molien_series(T, IR) # molien series as fraction field element
    F = parent(molien) # fraction field of univariate polynomial ring in t over QQ

    generators = elem_type(R)[] # list for generators
    
    if debug
        println("Molien series:")
        println(molien)
        println()
    end

    while true
        # 2. compute hilbert series of subalgebra k[f_1, ..., f_m] (using Oscar function)
        # input is generators = f_1, ..., f_m and
        # T, t = polynomial_ring(QQ, :t) and F = parent(molien) needed for hilbert and molien series
        # output is hilbert series H, quotientring A and induced homomorphisms
        hilbert, # hilbert series
        A, # A = S/I
        projection, # S -> A = S/I, p |-> [p]
        bar_phi = # A -> R, [y_i] |-> f_i
            compute_hilbertseries(R, generators, T, F)
        
        # 3. difference = molien - hilbert = c_d t^d + higher terms
        # use molien theorem: if hilbert = molien then k[f_1, ..., f_m] = R^G
        difference = molien - hilbert

        if debug
            println("----------------------------------------")
            println("Number of generators: ", length(generators))
            println("Hilbert series:")
            println(hilbert)
            println("Molien - Hilbert:")
            println(difference)
            println()
        end

        if iszero(difference)

            if debug
                println("Hilbert series equals Molien series.")
                println("The generating system is complete.")
            end
            
            # convert generators into original ring if original ring was ungraded
            if original_R !== R
                return elem_type(original_R)[original_R(forget_grading(f)) for f in generators]
            end
            return generators
        end

        # d is next missing degree with c_d linear independent new invariants
        d, number_missing = next_missing_degree(difference)

        if debug
            println("Next degree: ", d)
            println("Missing independent invariants: ", number_missing)
            println()
        end

        # Noether bound: highest degree for generators <= |G|
        noether_bound = order(G) 
        d <= noether_bound || error("The required degree exceeds the Noether bound |G|.")

        # 4. compute invariants using reynolds operator, test for linear independency
        # use reynolds operator to compute new invariants, check for linear independency
        generators, added = add_missing_invariants(
                G,
                R,
                generators,
                A,
                projection, # S -> A = S/I, p |-> [p]
                bar_phi, # A -> R, [y_i] |-> f_i
                d,
                number_missing
            )

        if debug
            println("Added invariants of degree ", d, ":")
            for f in added
                println(f)
            end
            println()
        end
    end
end
