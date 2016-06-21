//
// Created by will on 3/6/16.
//

#include "StringRelation.h"

namespace Vlab {
namespace Theory {

const int StringRelation::VLOG_LEVEL = 25;

StringRelation::StringRelation()
    : type_(Type::NONE),
      var_track_map_(nullptr) {
  num_tracks_ = 0;
}

StringRelation::StringRelation(Type t, std::shared_ptr<std::map<std::string, int>> var_map, std::vector<Subrelation> subrels,
                               size_t ntracks)
    : type_(t),
      var_track_map_(var_map),
      subrelations_(subrels),
      num_tracks_(ntracks) {
}

StringRelation::~StringRelation() {
}

StringRelation::StringRelation(const StringRelation &other)
    : type_(other.type_),
      var_track_map_(other.var_track_map_),
      subrelations_(other.subrelations_),
      num_tracks_(other.num_tracks_) {
}

StringRelation_ptr StringRelation::clone() const {
  return new StringRelation(*this);
}

//TODO: Check if the relations are equal...
StringRelation_ptr StringRelation::combine(StringRelation_ptr other_relation) {
  StringRelation_ptr result_relation = nullptr;
  //if (var_track_map != other_relation->get_variable_track_map()) {
  //  LOG(ERROR)<< "error in stringrelation combine: track maps are not identical";
  //  return nullptr;
  //}
  // combine their relations
  std::vector<Subrelation> subrels(this->subrelations_);
  subrels.insert(subrels.end(), other_relation->subrelations_.begin(), other_relation->subrelations_.end());
  result_relation = new StringRelation(StringRelation::Type::INTERSECT, this->var_track_map_, subrels,
                                       this->var_track_map_->size());
  return result_relation;
}

void StringRelation::add_subrelation(StringRelation::Subrelation subrel) {
  this->subrelations_.push_back(subrel);
}

std::vector<StringRelation::Subrelation> StringRelation::get_subrelation_list() {
  return subrelations_;
}

void StringRelation::set_type(Type type) {
  this->type_ = type;
}

StringRelation::Type StringRelation::get_type() const {
  return this->type_;
}

int StringRelation::get_variable_index(std::string name) const {
  auto iter = var_track_map_->find(name);
  if (iter == var_track_map_->end()) {
    return -1;
  }
  return iter->second;
}

void StringRelation::set_num_tracks(size_t ntracks) {
  this->num_tracks_ = ntracks;
}

size_t StringRelation::get_num_tracks() const {
  return this->var_track_map_->size();
}

std::shared_ptr<std::map<std::string, int>> StringRelation::get_variable_track_map() {
  return this->var_track_map_;
}

void StringRelation::set_variable_track_map(std::shared_ptr<std::map<std::string, int>> track_map) {
  this->var_track_map_ = track_map;
}

} /* namespace Theory */
} /* namespace Vlab */
