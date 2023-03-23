use crate::utils::assert_matches;

use super::*;

#[test]
fn error_file_doesnt_exist() {
    assert_matches!(read_to_leaked("file/doesnt/exist.hk"), Err(Error::IO(_)))
}

#[test]
fn error_file_was_directory() {
    assert_matches!(write("src", "foo"), Err(Error::InputFileWasDirectory(_)))
}

#[test]
fn error_file_was_root() {
    assert_matches!(write("/", "foo"), Err(Error::InputFileWasDirectory(_)))
}
