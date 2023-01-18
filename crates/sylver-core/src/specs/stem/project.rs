use std::fmt::Formatter;

use serde::de::value::MapAccessDeserializer;
use serde::de::{Error, MapAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::{builtin_langs::BuiltinLang, specs::stem::location::StemLocation};

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ProjectLang {
    Builtin(BuiltinLang),
    Custom(StemLocation),
}

impl Serialize for ProjectLang {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            ProjectLang::Builtin(b) => serializer.serialize_str(&b.to_string()),
            ProjectLang::Custom(c) => c.serialize(serializer),
        }
    }
}

impl<'de> Deserialize<'de> for ProjectLang {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ProjectLangVisitor {}

        impl<'de> Visitor<'de> for ProjectLangVisitor {
            type Value = ProjectLang;

            fn expecting(&self, formatter: &mut Formatter) -> std::fmt::Result {
                formatter.write_str("language name, git url or location object")
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: Error,
            {
                Ok(v.into())
            }

            fn visit_map<A>(self, map: A) -> Result<Self::Value, A::Error>
            where
                A: MapAccess<'de>,
            {
                let location: StemLocation =
                    Deserialize::deserialize(MapAccessDeserializer::new(map))?;
                Ok(ProjectLang::Custom(location))
            }
        }

        deserializer.deserialize_any(ProjectLangVisitor {})
    }
}

impl From<&str> for ProjectLang {
    fn from(value: &str) -> Self {
        value
            .try_into()
            .map(ProjectLang::Builtin)
            .unwrap_or_else(|_| ProjectLang::Custom(value.into()))
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(untagged)]
pub enum ProjectConfigStem {
    Flat(ProjectStem),
    Nested { projects: Vec<ProjectStem> },
}

impl ProjectConfigStem {
    pub fn projects(&'_ self) -> Box<dyn '_ + Iterator<Item = &ProjectStem>> {
        match self {
            ProjectConfigStem::Flat(p) => Box::new(std::iter::once(p)),
            ProjectConfigStem::Nested { projects } => Box::new(projects.iter()),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
pub struct ProjectStem {
    pub include: Vec<String>,
    #[serde(default)]
    pub exclude: Vec<String>,
    pub language: ProjectLang,
    #[serde(default)]
    pub rulesets: Vec<StemLocation>,
}
