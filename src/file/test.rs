use crate::utils::assert_matches;

use super::*;

#[test]
fn error_file_doesnt_exist() {
    assert_matches!(FileInfo::new("file/doesnt/exist.hk"), Err(Error::IO(_)))
}

#[test]
fn error_file_was_directory() {
    assert_matches!(FileInfo::new("/"), Err(Error::InputFileWasDirectory(_)))
}
