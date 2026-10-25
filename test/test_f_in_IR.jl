include("../src/f_in_IR.jl")

# test function for programm 2 f in IR

# input F = [f_1, ..., f_m] generators of invariant ring R^G = k[f_1, ..., f_m]
# and polynomial f in R = k[x_1, ..., x_n]
# output is (belongs, g) where `belongs` is "true" if f is in R^G and "false" if not
# and if f is in R^G then g is polynomial in k[y_1, ..., y_m] with f = g(f_1, ..., f_m)

# edge case: univariate polynomial; empty list of generators; constant polynomial; 
# invalid case: f not in R; not all f_1, ..., f_m in same ring
# f not a field or ring element

# [(F::AbstractVector, f::RingElem)]
test_list = [
    # multivariate example over QQ with f in IR
    let
        R, (x, y) = polynomial_ring(QQ, [:x, :y])
        F = [
            x^2 + y^2,
            x^4 + y^4,
            -x^3*y + x*y^3
        ]
        f = (x^2 + y^2)^2 + -x^3*y + x*y^3
        (F, f)
    end,
    # multivariate example over QQ(sqrt(2)) with f in IR
    let
        K, squareroot2 = quadratic_field(2)
        R, (x, y) = graded_polynomial_ring(K, [:x, :y])
        F = [
            x^2 + y^2,
            9*x^8 + 28*x^6*y^2 + 70*x^4*y^4 +
                28*x^2*y^6 + 9*y^8,
            -x^7*y + 7*x^5*y^3 - 7*x^3*y^5 + x*y^7
        ]
        f = x^2 + y^2
        (F, f)
    end,
    # reflection group B3 (symmetry group of the cube) with f in IR
    let
        R, (x, y, z) = polynomial_ring(QQ, [:x, :y, :z])
        F = [
            x^2 + y^2 + z^2,
            x^4 + y^4 + z^4,
            x^6 + y^6 + z^6
        ]
        f = 5(x^4 + y^4 + z^4) * (x^2 + y^2 + z^2)^4
        (F, f)
    end,
    # univariate example with f in IR
    let
        R, (x,) = polynomial_ring(QQ, [:x])
        F = [x^2]
        f = x^8
        (F, f)
    end,
    # test for first function, f is a field element
    let
        F = QQFieldElem[]
        f = QQ(7//3)
        (F, f)
    end,
    let
        R, (x, y) = polynomial_ring(QQ, [:x, :y])
        F = elem_type(R)[]
        f = QQ(7//3)
        (F, f)
    end,  
    # test for second function, f is a constant polynomial
    let
        R, (x, y) = polynomial_ring(QQ, [:x, :y])
        F = elem_type(R)[]
        f = R(3)
        (F, f)
    end,  
    # multivariate example over QQ with f not in IR
    let
        R, (x, y) = polynomial_ring(QQ, [:x, :y])
        F = [
            x^2 + y^2,
            x^4 + y^4,
            -x^3*y + x*y^3
        ]
        f = x
        (F, f)
    end,
    # multivariate example over QQ(sqrt(2)) with f not in IR
    let
        K, squareroot2 = quadratic_field(2)
        R, (x, y) = polynomial_ring(K, [:x, :y])
        F = [
            x^2 + y^2,
            9*x^8 + 28*x^6*y^2 + 70*x^4*y^4 +
                28*x^2*y^6 + 9*y^8,
            -x^7*y + 7*x^5*y^3 - 7*x^3*y^5 + x*y^7
        ]
        f = x^2 + y
        (F, f)
    end,
    # reflection group B3 (symmetry group of the cube) with f not in IR
    let
        R, (x, y, z) = polynomial_ring(QQ, [:x, :y, :z])
        F = [
            x^2 + y^2 + z^2,
            x^4 + y^4 + z^4,
            x^6 + y^6 + z^6
        ]
        f = x^2 + y^2 + z
        (F, f)
    end,
    # univariate example with f not in IR
    let
        R, (x,) = polynomial_ring(QQ, [:x])
        F = [x^2]
        f = x
        (F, f)
    end,
    # test for second function, f is not a constant polynomial
    let
        R, (x, y) = polynomial_ring(QQ, [:x, :y])
        F = elem_type(R)[]
        f = x 
        (F, f)
    end,
    # invalid cases:
    # test for first function, f is a field element but wrong field
    let
        F = QQFieldElem[7//3]
        K, a = quadratic_field(2)
        f = a
        (F, f)
    end,
    # f not a field element nor a polynomial in k[x_1, ..., x_n] where k is a field
    (ZZRingElem[], ZZ(3)),
    #f not in R 
    let
        R, (x, y) = polynomial_ring(QQ, [:x, :y])
        S, (z,) = polynomial_ring(QQ, [:z])
        F = [
            x^2 + y^2,
            x^4 + y^4,
            -x^3*y + x*y^3
        ]
        f = z
        (F, f)
    end,  
    #not all f_1, ..., f_m in same ring
    let
        R, (x, y) = polynomial_ring(QQ, [:x, :y])
        S, (v, w) = polynomial_ring(QQ, [:v, :w])
        F = [
            x^2 + y^2,
            v^2 + w^2
        ]
        f = x^2 + y^2
        (F, f)
    end,
    # k not a field
    let
        R, (x, y) = polynomial_ring(ZZ, [:x, :y])
        F = elem_type(R)[]
        f = R(2)
        (F, f)
    end
]

# test membership decisions and representations
function test(test_list)
    expected_errors = Dict(
        13 => "All generators and f must belong to the same field.",
        14 => "The input f must be a field or polynomial ring element over a field.",
        15 => "All generators and f must belong to the same polynomial ring.",
        16 => "All generators and f must belong to the same polynomial ring.",
        17 => "The coefficient ring must be a field."
    )

    # membership is true for test 1 to 7 and wrong for test 8 to 12
    expected_membership = Dict(i => i <= 7 for i in 1:12)

    for (i, (F, f)) in enumerate(test_list)
        # catch expected errors
        if haskey(expected_errors, i)
            rejected = false
            try
                membership_representation(F, f)
            catch err
                sprint(showerror, err) == expected_errors[i] || rethrow()
                rejected = true
                println("Test $i: expected error (", sprint(showerror, err), ")")
            end
            rejected || error("Test $i failed: invalid input was accepted.")
            continue
        end

        # `membership_representation` should run and give a result
        belongs, h = membership_representation(F, f)
        belongs == expected_membership[i] || error("Test $i failed: membership test wrong.")

        if belongs
            if h isa Union{PolyRingElem, MPolyRingElem}
                represented_f = evaluate(h, F) # `represented_f` = h(f_1, ..., f_m)
            else
                represented_f = h # for constant h
            end            
            represented_f == f || error("Test $i failed: wrong representation.")
        else
            h === nothing || error("Test $i failed: expected no representation.")
        end
        println("Test $i: passed")
    end
    return nothing
end

test(test_list)

