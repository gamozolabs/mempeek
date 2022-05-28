///! Basic constraints

use crate::{Error, Result, Value};

/// Different constraints we can apply on a value
#[derive(Debug, Clone, Copy)]
pub enum Constraint {
    /// `=`
    Equal(Value),
    
    /// `!`
    NotEqual(Value),

    /// `>`
    Greater(Value),

    /// `>=`
    GreaterEqual(Value),

    /// `<`
    Less(Value),

    /// `<=`
    LessEqual(Value),
}

impl Constraint {
    /// Replace the value with a new one
    pub fn update_val(&mut self, val: Value) {
        match self {
            Self::Greater(ref mut rhs) |
            Self::GreaterEqual(ref mut rhs) |
            Self::Less(ref mut rhs) |
            Self::LessEqual(ref mut rhs) |
            Self::Equal(ref mut rhs) => *rhs = val,
            Self::NotEqual(ref mut rhs) => *rhs = val,
        }
    }

    /// Check a condition
    pub fn check(&self, lhs: Value) -> bool {
        match *self {
            Self::Greater(rhs)      => lhs >  rhs,
            Self::GreaterEqual(rhs) => lhs >= rhs,
            Self::Less(rhs)         => lhs <  rhs,
            Self::LessEqual(rhs)    => lhs <= rhs,
            Self::Equal(rhs)        => lhs == rhs,
            Self::NotEqual(rhs)     => lhs != rhs,
        }
    }

    /// Create a new constraint from `s` using `val` as the type for the value
    pub fn from_str_value(s: &str, val: Option<Value>) -> Result<Self> {
        if s.starts_with("=") {
            if let Some(mut val) = val {
                val.update_str(&s[1..])?;
                Ok(Constraint::Equal(val))
            } else {
                Ok(Constraint::Equal(Value::U8(0)))
            }
        } else if s.starts_with("!") {
            if let Some(mut val) = val {
                val.update_str(&s[1..])?;
                Ok(Constraint::NotEqual(val))
            } else {
                Ok(Constraint::NotEqual(Value::U8(0)))
            }
        } else if s.starts_with(">=") {
            if let Some(mut val) = val {
                val.update_str(&s[2..])?;
                Ok(Constraint::GreaterEqual(val))
            } else {
                Ok(Constraint::GreaterEqual(Value::U8(0)))
            }
        } else if s.starts_with(">") {
            if let Some(mut val) = val {
                val.update_str(&s[1..])?;
                Ok(Constraint::Greater(val))
            } else {
                Ok(Constraint::Greater(Value::U8(0)))
            }
        } else if s.starts_with("<=") {
            if let Some(mut val) = val {
                val.update_str(&s[2..])?;
                Ok(Constraint::LessEqual(val))
            } else {
                Ok(Constraint::LessEqual(Value::U8(0)))
            }
        } else if s.starts_with("<") {
            if let Some(mut val) = val {
                val.update_str(&s[1..])?;
                Ok(Constraint::Less(val))
            } else {
                Ok(Constraint::Less(Value::U8(0)))
            }
        } else {
            Err(Error::InvalidConstraint)
        }
    }
}

