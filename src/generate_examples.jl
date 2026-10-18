# simplify polynomials, usefull for generators
function simplify_polynomial(f)
    iszero(f) && return f # cant divide through 0
    g = divexact(f, content(f)) # content gives back (rational) gcd
    if leading_coefficient(g) < 0
        g = -g # leading coefficient should be positive
    end
    return g
end

# example for programm 1, generators of the invariant ring
include("generators.jl")

# compute generators of the invariant ring of the reflection group of the cube
R_B3, (x_B3, y_B3, z_B3) = graded_polynomial_ring(QQ, [:x, :y, :z])
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
G_B3 = matrix_group(QQ, [s1, s2, s3])

generators_B3 = compute_generators(R_B3, G_B3; debug = false)
# simplify generators for better readability
generators_B3_simplified = simplify_polynomial.(generators_B3)

println("Example 1: Generators for invariant ring of the reflection group of the cube B3.")
println("F = (")
println.(generators_B3_simplified)
println(")")
println()
println("_________________________________________________")
println()

# examples for programm 2, membership and representation of f in R^G
include("f_in_IR.jl")

# C2
R_C2, (x_C2, y_C2) = graded_polynomial_ring(QQ, [:x, :y])
G_C2 = matrix_group(QQ, [identity_matrix(QQ, 2), (-identity_matrix(QQ, 2))])
generators_C2 = compute_generators(R_C2, G_C2; debug = false)
# simplify generators is not necessary since they already are simplified
# generators_C2_simplified = simplify_polynomial.(generators_C2)
f_C2 = x_C2^6 + x_C2^3 * y_C2^3 
belongs_C2, h_C2 = membership_representation(generators_C2, f_C2)

println("Example 2.1: Membership in invariant ring and representation; G = C2.")
println()
println("Generators of the invarinat ring: F = (")
println.(generators_C2)
println(")")
println()
println("Representation for f = x^6 + x^3 * y^3")
println("h = ", h_C2)
println()
println("_________________________________________________")
println()

# B3
# f =   (x_B3^2 + y_B3^2 + z_B3^2) * 
#       (x_B3^4 + y_B3^4 + z_B3^4) - 
#       (x_B3^6 + y_B3^6 + z_B3^6)
f_B3 =  x_B3^4 * y_B3^2 + x_B3^4 * z_B3^2 + x_B3^2 * y_B3^4 +
        x_B3^2 * z_B3^4 + y_B3^4 * z_B3^2 + y_B3^2 * z_B3^4
belongs_B3, h_B3 = membership_representation(generators_B3_simplified, f_B3)
println("Example 2.2: Membership in invariant ring and representation; G = B3.")
println()
println("Generators of the invarinat ring: F = (")
println.(generators_B3_simplified)
println(")")
println()
println("Representation for f = x^4 * y^2 + x^4 * z^2 + x^2 * y^4 +
        x^2 * z^4 + y^4 * z^2 + y^2 * z^4")
println("h = ", h_B3)
println()
println("_________________________________________________")
println()

# example for programm 3, ideal of relations

include("relations_ideal.jl")

# C2

I_F_C2, GG_y_C2 = relations_ideal(generators_C2, R_C2)
println("Example 3.2: Ideal of relations of C2.")
println()
println("Generators of the invarinat ring: F = (")
println.(generators_C2)
println(")")
println()
println("I_F = ", I_F_C2)
println()
println("With groebner basis ")
println.("GG = ", GG_y_C2)
println()
println()


# C4
R_C4, (x, y) = graded_polynomial_ring(QQ, [:x, :y])
G_C4 = matrix_group(QQ, [matrix(QQ, 2, 2, [0, -1, 1, 0])])
generators_C4 = compute_generators(R_C4, G_C4; debug = false)
generators_C4_simplified = simplify_polynomial.(generators_C4)
I_F_C4, GG_y_C4 = relations_ideal(generators_C4_simplified, R_C4)
println("Example 3.2: Ideal of relations of C4.")
println()
println("Generators of the invarinat ring: F = (")
println.(generators_C4_simplified)
println(")")
println()
println("I_F = ", I_F_C4)
println()
println("With groebner basis ")
println.("GG = ", GG_y_C4)

# verify example in ideals, varietes and algorithms
F_book = [x^2 + y^2, x^3 * y - x * y^3, x^2 * y^2]
I_F_book, GG_y_book = relations_ideal(F_book, R_C4)
println()
println("If F = (x^2 + y^2, x^3 * y - x * y^3, x^2 * y^2)")
println("Then I_F = ", I_F_book)
println()
println()

# C2 on 3x3
R_C2_3x3, (x_C2_3x3, y_C2_3x3, z_C2_3x3) = graded_polynomial_ring(QQ, [:x, :y, :z])
G_C2_3x3 = matrix_group(QQ, [identity_matrix(QQ, 3), (-identity_matrix(QQ, 3))])
generators_C2_3x3 = compute_generators(R_C2_3x3, G_C2_3x3; debug = false)
generators_C2_3x3_simplified = simplify_polynomial.(generators_C2_3x3)


I_F_C2_3x3, GG_y_C2_3x3 = relations_ideal(generators_C2_3x3, R_C2_3x3)
println("Example 3.3: Ideal of relations of C2 on QQ[x, y, z].")
println()
println("Generators of the invarinat ring: F = (")
println.(generators_C2_3x3_simplified)
println(")")
println()
println("I_F = ", I_F_C2_3x3)
println()
println("With groebner basis ")
println.("GG = ", GG_y_C2_3x3)
println()
println()

# B3
I_F_B3, GG_y_B3 = relations_ideal(generators_B3_simplified, R_B3)
println("Example 3.4: Ideal of relations of B3 on QQ[x, y, z].")
println()
println("Generators of the invarinat ring: F = (")
println.(generators_B3_simplified)
println(")")
println()
println("I_F = ", I_F_B3)
println()
println("With groebner basis ")
println.("GG = ", GG_y_B3)
println()
println()