%builtins output pedersen range_check ecdsa bitwise ec_op keccak poseidon

func main(
    output_ptr: felt*,
    pedersen_ptr: felt*,
    range_check_ptr: felt*,
    ecdsa_ptr: felt*,
    bitwise_ptr: felt*,
    ec_op_ptr: felt*,
    keccak_ptr: felt*,
    poseidon_ptr: felt*,
) -> (
    output_ptr: felt*,
    pedersen_ptr: felt*,
    range_check_ptr: felt*,
    ecdsa_ptr: felt*,
    bitwise_ptr: felt*,
    ec_op_ptr: felt*,
    keccak_ptr: felt*,
    poseidon_ptr: felt*,
) {
    // Call fib(1, 1, 10).
    let result: felt = fib(1, 1, 10);

    // Make sure the 10th Fibonacci number is 144.
    // assert result = 144;
    [output_ptr] = result;
    let output_ptr = output_ptr + 1;
    return (
        output_ptr,
        pedersen_ptr,
        range_check_ptr,
        ecdsa_ptr,
        bitwise_ptr,
        ec_op_ptr,
        keccak_ptr,
        poseidon_ptr,
    );
}

func fib(first_element, second_element, n) -> (res: felt) {
    jmp fib_body if n != 0;
    tempvar result = second_element;
    return (second_element,);

    fib_body:
    tempvar y = first_element + second_element;
    return fib(second_element, y, n - 1);
}