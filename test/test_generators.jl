include("../src/generators.jl")

# test function for programm 1 generators

# input R = k[x_1, ..., x_n], G <= Gl(n,k), `debug` boolian
# check if |G| < infty, char(k) = 0, degree(G) = number of variables of R
# and G and R must be over the same field k
# output f_1, ..., f_m with R^G = k[f_1, ..., f_m]

# edge cases: univariate polynomials; one generator
# invalid cases: char(K) != 0; |G| = infty; degree(G)!= number of variables of R;
# G and R not over the same field

# [(ring, group)]
test_list = [
    # multivariat C4
    let
        R, _ = graded_polynomial_ring(QQ, [:x, :y])
        G = matrix_group(QQ, [matrix(QQ, 2, 2, [0, -1, 1, 0])])
        (R, G)
    end,
    # C8
    let
        K, squareroot2 = quadratic_field(2)
        R, _ = polynomial_ring(K, [:x, :y])
        g = (1 / squareroot2) * matrix(K, 2, 2, [1, -1, 1, 1])
        G = matrix_group(K, [g])
        (R, G)
    end,
    # reflection group B3 (symmetry group of the cube)
    let
        R, _ = polynomial_ring(QQ, [:x, :y, :z])
        s1 = matrix(QQ, 3, 3, [
            0, 1, 0,
            1, 0, 0,
            0, 0, 1
        ])
        s2 = matrix(QQ, 3, 3, [
            1, 0, 0,
            0, 0, 1,
            0, 1, 0
        ])
        s3 = matrix(QQ, 3, 3, [
            1, 0, 0,
            0, 1, 0,
            0, 0, -1
        ])
        G = matrix_group(QQ, [s1, s2, s3])
        (R, G)
    end,
    # univariat, isomorphic to C2
    let
        R, _ = polynomial_ring(QQ, [:x])
        G = matrix_group(QQ, [matrix(QQ, 1, 1, [-1])])
        (R, G)
    end,
    # char(k) != 0
    let
        K3 = GF(3)
        R, _ = polynomial_ring(K3, [:x])
        G = matrix_group(K3, [matrix(K3, 1, 1, [-1])])
        (R, G)
    end,
    # |G| = infty (isomorphic to (ZZ, +))
    let
        R, _ = polynomial_ring(QQ, [:x, :y])
        G = matrix_group(QQ, [matrix(QQ, 2, 2, [1, 1, 0, 1])])
        (R, G)
    end,    
    # number of variables != degree(G)
    let
        R, _ = polynomial_ring(QQ, [:x, :y])
        G = matrix_group(QQ, [matrix(QQ, 1, 1, [-1])])
        (R, G)
    end,
    let
        R, _ = polynomial_ring(QQ, [:x])
        G = matrix_group(QQ, [matrix(QQ, 2, 2, [0, -1, 1, 0])])
        (R, G)
    end,
    # R = K
    (QQ, nothing),
    let
        R, _ = polynomial_ring(QQ, [:x, :y])
        K, squareroot2 = quadratic_field(2)
        g = (1 / squareroot2) * matrix(K, 2, 2, [1, -1, 1, 1])
        G = matrix_group(K, [g])
        (R, G)
    end,
    # K not a field
    let
        R, _ = polynomial_ring(ZZ, [:x, :y])
        G = matrix_group(QQ, [matrix(ZZ, 2, 2, [0, -1, 1, 0])])
        (R, G)
    end,    
]

# test if k[f_1, ..., f_m] == R^G 
# for computed `generators` [f_1, ..., f_m]
function verify_generators(R::MPolyRing, G::MatGroup, generators)
    # Oscar function `invariant_ring` needs graded ring as input
    if !(R isa MPolyDecRing)
        R, _ = grade(R)
        generators = elem_type(R)[R(f) for f in generators]
    end
    IR = invariant_ring(R, G)
    oscar_generators = fundamental_invariants(IR) # Oscar function for generators of IR

    # test if k[f_1, ..., f_m] subseteq R^G
    # by testing for invariancy
    for f in generators
        if reynolds_operator(IR, f) != f # test if generators are invariants
            println("Generators are not invariants, k[f_1, ..., f_m] is not a subset of R^G.")
            return false 
        end
    end

    # test if R^G subseteq k[f_1, ..., f_m]
    # by testing for subalgebra membership with Oscar function
    if isempty(generators)
        return all(f -> total_degree(f) == 0, oscar_generators) # test for constant generators
    end

    for f in oscar_generators
        belongs, _ = subalgebra_membership(
            forget_grading(f), [forget_grading(g) for g in generators]
        ) # true for `oscar_generator` \in k[f_1, ..., f_m]
        if belongs == false
            println("R^G is not a subset of k[f_1, ..., f_m].")
            return false
        end
    end
    return true
end

# compute `generators` for test list and verify them
function test(test_list)
    expected_errors = Dict(
        5 => "The coefficient field must have characteristic zero.",
        6 => "G must be finite.",
        7 => "The degree of G must equal the number  of variables of R.",
        8 => "The degree of G must equal the number  of variables of R.",
        10 => "G and R must be defined over the same field.",
        11 => "The coefficient ring must be a field." # to satisfy convention
    )
    for (i, (R, G)) in enumerate(test_list)
        if haskey(expected_errors, i) # these inputs must be rejected by `compute_generators`
            rejected = false
            try
                compute_generators(R, G; debug = false)
            catch err
                sprint(showerror, err) == expected_errors[i] || rethrow()
                rejected = true
                println("Test $i: expected error (", sprint(showerror, err), ")")
            end
            rejected || error("Test $i failed: invalid input was accepted.")
            continue
        end

        generators = compute_generators(R, G; debug = false)
        if G === nothing # if R = k
            correct = isempty(generators)
        else # R is not k, verify via Oscar function
            correct = verify_generators(R, G, generators)
        end        
        correct || error("Test $i failed: incorrect generators.")
        println("Test $i: passed")
    end
    return nothing
end


test(test_list)
