//
// Created by will on 3/6/16.
//

#include "StringRelation.h"

namespace Vlab {
namespace Theory {

const int StringRelation::VLOG_LEVEL = 25;

StringRelation::StringRelation()
    : type(Type::NONE),
      var_track_map(nullptr) {
  num_tracks = 0;
}

StringRelation::StringRelation(Type t, std::map<std::string, int> *var_map, std::vector<Subrelation> subrels,
                               size_t ntracks)
    : type(t),
      var_track_map(var_map),
      subrelations(subrels),
      num_tracks(ntracks) {
}

StringRelation::~StringRelation() {
}

StringRelation::StringRelation(const StringRelation &other)
    : type(other.type),
      var_track_map(other.var_track_map),
      subrelations(other.subrelations),
      num_tracks(other.num_tracks) {
}

StringRelation_ptr StringRelation::clone() const {
  return new StringRelation(*this);
}

//TODO: Check if the relations are equal...
StringRelation_ptr StringRelation::combine(StringRelation_ptr other_relation) {
  StringRelation_ptr result_relation = nullptr;
  if (var_track_map != other_relation->get_variable_track_map()) {
    LOG(ERROR)<< "error in stringrelation combine: track maps are not identical";
    return nullptr;
  }

  // combine their relations
  std::vector<Subrelation> subrels(this->subrelations);
  subrels.insert(subrels.end(), other_relation->subrelations.begin(), other_relation->subrelations.end());
  result_relation = new StringRelation(StringRelation::Type::INTERSECT, this->var_track_map, subrels,
                                       this->var_track_map->size());
  return result_relation;
}

void StringRelation::add_subrelation(StringRelation::Subrelation subrel) {
  this->subrelations.push_back(subrel);
}

std::vector<StringRelation::Subrelation> StringRelation::get_subrelation_list() {
  return subrelations;
}

void StringRelation::set_type(Type type) {
  this->type = type;
}

StringRelation::Type StringRelation::get_type() const {
  return this->type;
}

int StringRelation::get_variable_index(std::string name) const {
  auto iter = var_track_map->find(name);
  if (iter == var_track_map->end()) {
    return -1;
  }
  return iter->second;
}

void StringRelation::set_num_tracks(size_t ntracks) {
  this->num_tracks = ntracks;
}

size_t StringRelation::get_num_tracks() const {
  return this->var_track_map->size();
}

std::map<std::string, int>* StringRelation::get_variable_track_map() {
  return this->var_track_map;
}
;

void StringRelation::set_variable_track_map(std::map<std::string, int>* track_map) {
  this->var_track_map = track_map;
}

} /* namespace Theory */
} /* namespace Vlab */
