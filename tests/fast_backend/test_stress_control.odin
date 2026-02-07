package test_stress_control

foreign import libc "system:c"
foreign libc {
	exit :: proc "c" (code: i32) ---
}

check :: proc(cond: bool, code: i32) {
	if !cond {
		exit(code)
	}
}

// Fibonacci via loop — many branches and variable reassignments
fib :: proc(n: int) -> int {
	if n <= 1 { return n }
	a := 0
	b := 1
	for i := 2; i <= n; i += 1 {
		c := a + b
		a = b
		b = c
	}
	return b
}

// GCD via loop — while-style loop with modulo
gcd :: proc(a: int, b: int) -> int {
	x := a
	y := b
	for y != 0 {
		t := y
		y = x % y
		x = t
	}
	return x
}

// Chained if/else — many branches with data flow
classify :: proc(x: int) -> int {
	if x < 0 {
		return -1
	} else if x == 0 {
		return 0
	} else if x < 10 {
		return 1
	} else if x < 100 {
		return 2
	} else {
		return 3
	}
}

// Deep nesting
deep_nest :: proc(a: int, b: int, c: int) -> int {
	result := 0
	if a > 0 {
		if b > 0 {
			if c > 0 {
				result = a + b + c
			} else {
				result = a + b
			}
		} else {
			if c > 0 {
				result = a + c
			} else {
				result = a
			}
		}
	} else {
		result = 0
	}
	return result
}

// Loop with multiple exits
find_first :: proc(target: int) -> int {
	data := [8]int{5, 12, 3, 7, 15, 1, 9, 11}
	for val, idx in data {
		if val == target {
			return idx
		}
	}
	return -1
}

// Complex: accumulator with conditional adds
complex_loop :: proc(n: int) -> int {
	sum := 0
	prod := 1
	for i := 1; i <= n; i += 1 {
		if i % 3 == 0 {
			sum += i * 2
		} else if i % 2 == 0 {
			sum += i
		} else {
			prod *= i
			if prod > 1000 {
				prod = 1
			}
		}
	}
	return sum + prod
}

main :: proc() {
	check(fib(0)  == 0, 1)
	check(fib(1)  == 1, 2)
	check(fib(10) == 55, 3)
	check(fib(20) == 6765, 4)

	check(gcd(12, 8)   == 4, 10)
	check(gcd(100, 75) == 25, 11)
	check(gcd(17, 13)  == 1, 12)
	check(gcd(0, 5)    == 5, 13)

	check(classify(-5)  == -1, 20)
	check(classify(0)   ==  0, 21)
	check(classify(7)   ==  1, 22)
	check(classify(50)  ==  2, 23)
	check(classify(200) ==  3, 24)

	check(deep_nest(1, 1, 1) == 3, 30)
	check(deep_nest(1, 1, 0) == 2, 31)
	check(deep_nest(1, 0, 1) == 2, 32)
	check(deep_nest(1, 0, 0) == 1, 33)
	check(deep_nest(0, 1, 1) == 0, 34)

	check(find_first(7)  == 3, 40)
	check(find_first(5)  == 0, 41)
	check(find_first(11) == 7, 42)
	check(find_first(99) == -1, 43)

	r := complex_loop(15)
	// Manual trace:
	// i=1: odd, prod=1  sum=0
	// i=2: even, sum=2
	// i=3: %3, sum=2+6=8
	// i=4: even, sum=8+4=12
	// i=5: odd, prod=5  sum=12
	// i=6: %3, sum=12+12=24
	// i=7: odd, prod=35 sum=24
	// i=8: even, sum=24+8=32
	// i=9: %3, sum=32+18=50
	// i=10: even, sum=50+10=60
	// i=11: odd, prod=385 sum=60
	// i=12: %3, sum=60+24=84
	// i=13: odd, prod=5005>1000→1 sum=84
	// i=14: even, sum=84+14=98
	// i=15: %3, sum=98+30=128
	// result = 128 + 1 = 129
	check(r == 129, 50)

	exit(0)
}
