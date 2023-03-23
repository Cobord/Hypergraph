fn surjectivity() {
    use crate::finset::is_surjective;
    let mut cur_test : Vec<usize> = vec![];
    assert!(is_surjective(&cur_test));
    cur_test = vec![0];
    assert!(is_surjective(&cur_test));
    cur_test = vec![1];
    assert!(!is_surjective(&cur_test));
    cur_test = vec![2];
    assert!(!is_surjective(&cur_test));
    cur_test = vec![12490];
    assert!(!is_surjective(&cur_test));
    cur_test = vec![0,1,2];
    assert!(is_surjective(&cur_test));
    cur_test = vec![0,2,1];
    assert!(is_surjective(&cur_test));
    cur_test = vec![2,1];
    assert!(!is_surjective(&cur_test));
    cur_test = vec![0,3,1,2];
    assert!(is_surjective(&cur_test));
    cur_test = vec![1,1,2];
    assert!(!is_surjective(&cur_test));
    cur_test = vec![0,1,1,2];
    assert!(is_surjective(&cur_test));
}