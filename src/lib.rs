pub mod algebra;
pub mod algorithms;
pub mod structures;

pub struct Unchecked<T>(T);

impl<T> Unchecked<T> {
    pub fn new(value: T) -> Unchecked<T> {
        Unchecked(value)
    }

    /// # Safety
    /// The value might not be valid or might not follow invariants or construction rules
    pub unsafe fn get(&self) -> &T {
        &self.0
    }

    /// # Safety
    /// The value might not be valid or might not follow invariants or construction rules
    pub unsafe fn get_mut(&mut self) -> &mut T {
        &mut self.0
    }

    /// # Safety
    /// The value might not be valid or might not follow invariants or construction rules
    pub unsafe fn unwrap(self) -> T {
        self.0
    }
}

pub enum Checked<T> {
    Unchecked(Unchecked<T>),
    Checked(T),
}

impl<T> Checked<T> {
    pub fn get_checked(self) -> Option<T> {
        match self {
            Checked::Unchecked(_) => None,
            Checked::Checked(value) => Some(value),
        }
    }

    pub fn get_unchecked(self) -> Option<Unchecked<T>> {
        match self {
            Checked::Unchecked(value) => Some(value),
            Checked::Checked(_) => None,
        }
    }

    pub fn unwrap(self) -> Unchecked<T> {
        match self {
            Checked::Unchecked(value) => value,
            Checked::Checked(value) => Unchecked::new(value),
        }
    }
}
