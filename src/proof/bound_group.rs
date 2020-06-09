use super::bound::DescriptiveBound;
use super::Requirement;
use std::collections::BTreeSet;
use std::convert::identity;
use std::iter::Iterator;
use std::ops::Deref;

#[derive(Debug, Clone)]
pub struct BoundGroup<'a> {
    bounds: Vec<Option<DescriptiveBound<'a>>>,
    requirements: Vec<BTreeSet<usize>>,
    permutation_groups: Vec<BTreeSet<usize>>,
}

#[derive(Clone, Copy)]
pub struct BoundRef<'a: 'b, 'b> {
    id: usize,
    group: &'b BoundGroup<'a>,
}

#[derive(Clone, Copy)]
pub struct RequirementRef<'a: 'b, 'b> {
    id: usize,
    group: &'b BoundGroup<'a>,
}

pub struct Iter<'a: 'b, 'b> {
    group: &'b BoundGroup<'a>,
    bound_idx: usize,
}

impl<'a: 'b, 'b> BoundGroup<'a> {
    pub fn new() -> BoundGroup<'a> {
        BoundGroup {
            bounds: Vec::new(),
            requirements: Vec::new(),
            permutation_groups: Vec::new(),
        }
    }

    pub fn with_capacity(
        bounds: usize,
        requirements: usize,
        permutation_groups: usize,
    ) -> BoundGroup<'a> {
        BoundGroup {
            bounds: Vec::with_capacity(bounds),
            requirements: Vec::with_capacity(requirements),
            permutation_groups: Vec::with_capacity(permutation_groups),
        }
    }

    pub fn from_requirements(reqs: Vec<Requirement<'a>>) -> BoundGroup<'a> {
        let mut out = BoundGroup::with_capacity(reqs.len() * 2, reqs.len(), reqs.len() / 4);
        out.add_requirements(reqs);
        out
    }

    /// Adds bound to this BoundGroup. This adds it to the bounds slice and permutation_groups but
    /// does not add it to it's correct requirements group.
    pub fn add(&mut self, bound: DescriptiveBound<'a>) -> usize {
        // This is the index of the bound we are inserting.
        let this_idx = self.bounds.len();
        self.bounds.push(Some(bound.clone()));

        match self.permutation_groups.iter().position(|group| {
            group
                .iter()
                .filter_map(|grp_bound| {
                    Some(!self.bounds[*grp_bound].clone()?.permutes_with(&bound))
                })
                .next()
                .unwrap_or(false)
        }) {
            Some(perm_grp_idx) => {
                self.permutation_groups[perm_grp_idx].insert(this_idx);
            }
            None => {
                self.permutation_groups.push({
                    let mut new_set = BTreeSet::new();
                    new_set.insert(this_idx);
                    new_set
                });
            }
        }

        this_idx
    }

    /// Adds the requirements bounds to self.
    /// This creates a new requirements group in self.requirements containing all the bounds from
    /// this requirement.
    /// The requirements are also added to the correct permutation_groups group.
    pub fn add_requirement(&mut self, req: &Requirement<'a>) -> usize {
        let req_idx = self.requirements.len();
        let bounds = req.as_relation().bounds();
        let mut requirements_group = BTreeSet::new();
        for bound in bounds {
            requirements_group.insert(self.add(bound.simplify()));
        }
        self.requirements.push(requirements_group);
        req_idx
    }

    /// Adds all the requirements to self.
    /// (This calls self.add_requirement on each requirement).
    pub fn add_requirements(&mut self, reqs: Vec<Requirement<'a>>) {
        reqs.iter().for_each(|req| {
            self.add_requirement(req);
        });
    }

    /// Returns an iterator over all the bounds within self
    pub fn iter(&'b self) -> Iter<'a, 'b> {
        Iter {
            group: self,
            bound_idx: 0,
        }
    }

    /// Returns the maximum requirement ID.
    /// See RequirementRef.id() for more information.
    pub fn max_requirement_id(&self) -> usize {
        self.requirements.len()
    }

    /// This is garenteed not to change bound or requirement IDs.
    pub fn sub_bound(&self, bound: &DescriptiveBound<'a>) -> BoundGroup<'a> {
        let new_bounds = self
            .bounds
            .iter()
            .map(|old_bound| old_bound.as_ref()?.sub(bound))
            .collect();
        BoundGroup {
            bounds: new_bounds,
            requirements: self.requirements.clone(),
            permutation_groups: self.permutation_groups.clone(),
        }
    }
}

impl<'a: 'b, 'b> BoundRef<'a, 'b> {
    /// Returns the requirement
    pub fn requirement(&self) -> Option<RequirementRef<'a, 'b>> {
        Some(RequirementRef {
            id: self
                .group
                .requirements
                .iter()
                .position(|req_grp| req_grp.contains(&self.id))?,
            group: self.group,
        })
    }

    /// Returns an ID for this bound. This ID is garenteed to be unique among all other bounds in
    /// this BoundGroup and will have a maximum value of the total number of bounds.
    pub fn id(&self) -> usize {
        self.id
    }

    /// Returns a vector of all bounds which self must be permuted with.
    pub fn permutation_group(&self) -> Vec<BoundRef<'a, 'b>> {
        self.group
            .permutation_groups
            .iter()
            // Find the permutation group containing self.
            // self must be in only 1 group, so we can stop when we find one and unwrap since we
            // know one must exist.
            .find(|pg| pg.contains(&self.id))
            .unwrap()
            .iter()
            // Filter out invalid bounds and create BoundRefs
            .filter_map(|id| {
                if self.group.bounds[*id].is_some() {
                    Some(BoundRef {
                        id: *id,
                        group: self.group,
                    })
                } else {
                    None
                }
            })
            .collect()
    }
}

// I reckon this counts as a smart pointer?
// It's a reference to something, which provides additional functionality.
impl<'a: 'b, 'b> Deref for BoundRef<'a, 'b> {
    type Target = DescriptiveBound<'a>;
    fn deref(&self) -> &DescriptiveBound<'a> {
        // Using unwrap here may look like deref can panic! That would be bad.
        // Luckily, this can't happen. If we only ever create BoundRefs to bounds that are Some,
        // they cannot change since we hold a reference to the Vec.
        return self.group.bounds[self.id].as_ref().unwrap();
    }
}

impl<'a: 'b, 'b> RequirementRef<'a, 'b> {
    /// Returns the bounds that belong to this requirement
    pub fn bounds(&self) -> Vec<BoundRef<'a, 'b>> {
        self.group.requirements[self.id]
            .iter()
            .filter_map(|bound_id| {
                // Return a BoundRef if this is a valid bound
                if self.group.bounds[*bound_id].is_some() {
                    Some(BoundRef {
                        id: *bound_id,
                        group: self.group,
                    })
                } else {
                    None
                }
            })
            .collect()
    }

    /// Returns an ID for this requirement. This ID is garenteed to be unique among all other
    /// requirements in this BoundGroup and will have a maximum value of the total number of
    /// requirements.
    pub fn id(&self) -> usize {
        self.id
    }
}

impl<'a: 'b, 'b> Iterator for Iter<'a, 'b> {
    type Item = BoundRef<'a, 'b>;
    fn next(&mut self) -> Option<BoundRef<'a, 'b>> {
        // Find the index of the next valid bound.
        let this_idx = (&self.group.bounds[self.bound_idx..])
            .iter()
            .position(|bound| bound.is_some())?
            + self.bound_idx;
        // On the next iteration, try from the next index.
        self.bound_idx = this_idx + 1;
        // Return a BoundRef to this_idx
        Some(BoundRef {
            id: this_idx,
            group: self.group,
        })
    }
}
