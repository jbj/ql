fn get_sum(values:&[i32]) -> i32 {
	let mut sum = 0;
	let mut average = 0; // BAD: unused value

	for v in values {
		sum += v;
	}

	return sum;
}
