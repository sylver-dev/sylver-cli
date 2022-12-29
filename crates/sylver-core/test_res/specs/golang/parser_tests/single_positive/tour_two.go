package main

import "fmt"

func add(x int, y int) int {
	return 1 * 2 + x / y
}

func main() {
	fmt.Println(add(42, 13))
}