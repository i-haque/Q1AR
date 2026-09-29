from z3 import *


MAX_STEPS = 36


def check_k(k):

    solver = Solver()

    # Program variables at every step
    a = [Int(f"a_{i}") for i in range(MAX_STEPS + 1)]
    b = [Int(f"b_{i}") for i in range(MAX_STEPS + 1)]

    # Whether the loop is still executing
    active = [Bool(f"active_{i}") for i in range(MAX_STEPS + 1)]

    # Nondeterministic choice
    choice = [Bool(f"choice_{i}") for i in range(MAX_STEPS)]

    # Initial state
    solver.add(a[0] == 1)
    solver.add(b[0] == 1)
    solver.add(active[0] == True)

    for i in range(MAX_STEPS):

        # If the loop is active, a < 180
        solver.add(
            Implies(
                active[i],
                a[i] < 180
            )
        )

        # If the loop is active, execute one branch
        solver.add(
            Implies(
                active[i],

                If(
                    choice[i],

                    # TRUE branch
                    And(
                        b[i + 1] == b[i] + 3,
                        a[i + 1] == a[i] + 2 * b[i + 1]
                    ),

                    # FALSE branch
                    And(
                        b[i + 1] == b[i] + a[i],
                        a[i + 1] == a[i] + 5
                    )
                )
            )
        )

        # Determine whether the loop continues
        solver.add(
            Implies(
                active[i],
                active[i + 1] == (a[i + 1] < 180)
            )
        )

        # If the loop has already terminated,
        # keep the state unchanged.
        solver.add(
            Implies(
                Not(active[i]),
                And(
                    a[i + 1] == a[i],
                    b[i + 1] == b[i],
                    active[i + 1] == False
                )
            )
        )

    # We want a TERMINAL state
    solver.add(active[MAX_STEPS] == False)

    # Assertion condition
    solver.add(
        b[MAX_STEPS] == 190 + k
    )

    if solver.check() == sat:

        model = solver.model()

        print(f"k = {k}: UNSAFE")
        print("Run:")

        for i in range(MAX_STEPS):

            # Stop printing once loop has terminated
            if not is_true(model.eval(active[i])):
                break

            current_a = model.eval(a[i]).as_long()
            current_b = model.eval(b[i]).as_long()

            next_a = model.eval(a[i + 1]).as_long()
            next_b = model.eval(b[i + 1]).as_long()

            if is_true(model.eval(choice[i])):
                branch = "TRUE"
            else:
                branch = "FALSE"

            print(
                f"  {i}: "
                f"(a={current_a}, b={current_b}) "
                f"--{branch}--> "
                f"(a={next_a}, b={next_b})"
            )

        print(
            f"  Final: "
            f"a={model.eval(a[MAX_STEPS])}, "
            f"b={model.eval(b[MAX_STEPS])}"
        )

    else:
        print(f"k = {k}: SAFE")


# Check all values
for k in range(11):
    check_k(k)
    print()
