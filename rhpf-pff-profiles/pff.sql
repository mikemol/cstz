BEGIN;

-- ============================================================
-- PFF / RHPF relational profile (PostgreSQL)
-- ============================================================
-- Normative choices reflected here:
-- 1. Flat, document-scoped model.
-- 2. All local identifiers are document-local.
-- 3. Segment ranks are strictly increasing within one addr0.
-- 4. Shadows and class views are derived, never authoritative.
-- 5. Core tables are append-only in this reference profile.
-- ============================================================

CREATE TABLE rhpf_document (
  document_id          text PRIMARY KEY,
  version              text NOT NULL CHECK (version = '1.0'),
  identifier_scope     text NOT NULL CHECK (identifier_scope = 'document-local'),
  base_iri             text
);

CREATE TABLE rhpf_rank (
  document_id          text NOT NULL REFERENCES rhpf_document(document_id) ON DELETE CASCADE,
  rank_id              text NOT NULL,
  ordinal              integer NOT NULL CHECK (ordinal >= 0),
  label                text,
  note                 text,
  PRIMARY KEY (document_id, rank_id),
  UNIQUE (document_id, ordinal)
);

CREATE TABLE rhpf_patch (
  document_id          text NOT NULL REFERENCES rhpf_document(document_id) ON DELETE CASCADE,
  patch_id             text NOT NULL,
  rank_id              text NOT NULL,
  phase                text NOT NULL,
  left_boundary_id     text,
  right_boundary_id    text,
  label                text,
  meta                 jsonb,
  PRIMARY KEY (document_id, patch_id),
  FOREIGN KEY (document_id, rank_id) REFERENCES rhpf_rank(document_id, rank_id)
);

CREATE TABLE rhpf_boundary (
  document_id          text NOT NULL REFERENCES rhpf_document(document_id) ON DELETE CASCADE,
  boundary_id          text NOT NULL,
  PRIMARY KEY (document_id, boundary_id)
);

ALTER TABLE rhpf_patch
  ADD CONSTRAINT rhpf_patch_left_boundary_fk
  FOREIGN KEY (document_id, left_boundary_id)
  REFERENCES rhpf_boundary(document_id, boundary_id);

ALTER TABLE rhpf_patch
  ADD CONSTRAINT rhpf_patch_right_boundary_fk
  FOREIGN KEY (document_id, right_boundary_id)
  REFERENCES rhpf_boundary(document_id, boundary_id);

CREATE TABLE rhpf_port (
  document_id          text NOT NULL,
  boundary_id          text NOT NULL,
  port_name            text NOT NULL,
  role                 text,
  PRIMARY KEY (document_id, boundary_id, port_name),
  FOREIGN KEY (document_id, boundary_id)
    REFERENCES rhpf_boundary(document_id, boundary_id) ON DELETE CASCADE
);

CREATE TABLE rhpf_chart (
  document_id          text NOT NULL REFERENCES rhpf_document(document_id) ON DELETE CASCADE,
  chart_id             text NOT NULL,
  patch_id             text,
  root_ref             text NOT NULL,
  kind                 text,
  payload              jsonb,
  PRIMARY KEY (document_id, chart_id),
  FOREIGN KEY (document_id, patch_id)
    REFERENCES rhpf_patch(document_id, patch_id)
);

CREATE TABLE rhpf_addr0 (
  document_id          text NOT NULL REFERENCES rhpf_document(document_id) ON DELETE CASCADE,
  addr0_id             text NOT NULL,
  sort                 text,
  discovery_rank_id    text,
  payload              jsonb,
  meta                 jsonb,
  PRIMARY KEY (document_id, addr0_id),
  FOREIGN KEY (document_id, discovery_rank_id)
    REFERENCES rhpf_rank(document_id, rank_id)
);

CREATE TABLE rhpf_segment (
  document_id          text NOT NULL REFERENCES rhpf_document(document_id) ON DELETE CASCADE,
  segment_id           bigint GENERATED ALWAYS AS IDENTITY,
  addr0_id             text NOT NULL,
  segment_ordinal      integer NOT NULL CHECK (segment_ordinal >= 0),
  rank_id              text NOT NULL,
  patch_id             text NOT NULL,
  phase                text NOT NULL,
  PRIMARY KEY (document_id, segment_id),
  UNIQUE (document_id, addr0_id, segment_ordinal),
  UNIQUE (document_id, addr0_id, rank_id),
  FOREIGN KEY (document_id, addr0_id)
    REFERENCES rhpf_addr0(document_id, addr0_id) ON DELETE CASCADE,
  FOREIGN KEY (document_id, rank_id)
    REFERENCES rhpf_rank(document_id, rank_id),
  FOREIGN KEY (document_id, patch_id)
    REFERENCES rhpf_patch(document_id, patch_id)
);

CREATE TABLE rhpf_pair (
  document_id          text NOT NULL,
  pair_id              bigint GENERATED ALWAYS AS IDENTITY,
  segment_id           bigint NOT NULL,
  pair_ordinal         integer NOT NULL CHECK (pair_ordinal >= 0),
  chart_id             text NOT NULL,
  root_ref             text NOT NULL,
  role                 text NOT NULL CHECK (role IN ('principal', 'aux')),
  PRIMARY KEY (document_id, pair_id),
  UNIQUE (document_id, segment_id, pair_ordinal),
  FOREIGN KEY (document_id, segment_id)
    REFERENCES rhpf_segment(document_id, segment_id) ON DELETE CASCADE,
  FOREIGN KEY (document_id, chart_id)
    REFERENCES rhpf_chart(document_id, chart_id)
);

CREATE TABLE rhpf_route_step (
  document_id          text NOT NULL,
  pair_id              bigint NOT NULL,
  step_ordinal         integer NOT NULL CHECK (step_ordinal >= 0),
  kind                 text NOT NULL CHECK (kind IN ('child', 'field', 'pack', 'share', 'port')),
  arg_text             text,
  arg_int              integer,
  CHECK (
    (arg_text IS NOT NULL AND arg_int IS NULL) OR
    (arg_text IS NULL AND arg_int IS NOT NULL) OR
    (arg_text IS NULL AND arg_int IS NULL)
  ),
  PRIMARY KEY (document_id, pair_id, step_ordinal),
  FOREIGN KEY (document_id, pair_id)
    REFERENCES rhpf_pair(document_id, pair_id) ON DELETE CASCADE
);

CREATE TABLE rhpf_hop (
  document_id          text NOT NULL,
  pair_id              bigint NOT NULL,
  hop_ordinal          integer NOT NULL CHECK (hop_ordinal >= 0),
  boundary_id          text NOT NULL,
  side                 text NOT NULL CHECK (side IN ('left', 'right', 'both')),
  port_name            text NOT NULL,
  PRIMARY KEY (document_id, pair_id, hop_ordinal),
  FOREIGN KEY (document_id, pair_id)
    REFERENCES rhpf_pair(document_id, pair_id) ON DELETE CASCADE,
  FOREIGN KEY (document_id, boundary_id, port_name)
    REFERENCES rhpf_port(document_id, boundary_id, port_name)
);

CREATE TABLE rhpf_addr1 (
  document_id          text NOT NULL REFERENCES rhpf_document(document_id) ON DELETE CASCADE,
  addr1_id             text NOT NULL,
  rank_id              text NOT NULL,
  patch_id             text,
  ctor                 text NOT NULL CHECK (ctor IN ('refl', 'glue', 'transport', 'pack', 'compose', 'inverse', 'named')),
  src_addr0_id         text NOT NULL,
  dst_addr0_id         text NOT NULL,
  boundary_id          text,
  label                text,
  args                 jsonb,
  PRIMARY KEY (document_id, addr1_id),
  FOREIGN KEY (document_id, rank_id)
    REFERENCES rhpf_rank(document_id, rank_id),
  FOREIGN KEY (document_id, patch_id)
    REFERENCES rhpf_patch(document_id, patch_id),
  FOREIGN KEY (document_id, src_addr0_id)
    REFERENCES rhpf_addr0(document_id, addr0_id),
  FOREIGN KEY (document_id, dst_addr0_id)
    REFERENCES rhpf_addr0(document_id, addr0_id),
  FOREIGN KEY (document_id, boundary_id)
    REFERENCES rhpf_boundary(document_id, boundary_id)
);

CREATE TABLE rhpf_addr1_premise (
  document_id          text NOT NULL,
  addr1_id             text NOT NULL,
  premise_ordinal      integer NOT NULL CHECK (premise_ordinal >= 0),
  premise_addr1_id     text NOT NULL,
  PRIMARY KEY (document_id, addr1_id, premise_ordinal),
  FOREIGN KEY (document_id, addr1_id)
    REFERENCES rhpf_addr1(document_id, addr1_id) ON DELETE CASCADE,
  FOREIGN KEY (document_id, premise_addr1_id)
    REFERENCES rhpf_addr1(document_id, addr1_id)
);

CREATE TABLE rhpf_addr2 (
  document_id          text NOT NULL REFERENCES rhpf_document(document_id) ON DELETE CASCADE,
  addr2_id             text NOT NULL,
  rank_id              text NOT NULL,
  patch_id             text,
  ctor                 text NOT NULL CHECK (ctor IN ('coh', 'vcomp', 'hcomp', 'whisker', 'named2')),
  src_addr1_id         text NOT NULL,
  dst_addr1_id         text NOT NULL,
  label                text,
  args                 jsonb,
  PRIMARY KEY (document_id, addr2_id),
  FOREIGN KEY (document_id, rank_id)
    REFERENCES rhpf_rank(document_id, rank_id),
  FOREIGN KEY (document_id, patch_id)
    REFERENCES rhpf_patch(document_id, patch_id),
  FOREIGN KEY (document_id, src_addr1_id)
    REFERENCES rhpf_addr1(document_id, addr1_id),
  FOREIGN KEY (document_id, dst_addr1_id)
    REFERENCES rhpf_addr1(document_id, addr1_id)
);

CREATE TABLE rhpf_class_view (
  document_id          text NOT NULL REFERENCES rhpf_document(document_id) ON DELETE CASCADE,
  class_view_id        text NOT NULL,
  rank_id              text NOT NULL,
  phase                text NOT NULL,
  truncation           text NOT NULL,
  congruence           text NOT NULL,
  policy_uri           text,
  is_authoritative     boolean NOT NULL DEFAULT false CHECK (is_authoritative = false),
  PRIMARY KEY (document_id, class_view_id),
  FOREIGN KEY (document_id, rank_id)
    REFERENCES rhpf_rank(document_id, rank_id)
);

CREATE TABLE rhpf_class_member (
  document_id          text NOT NULL,
  class_view_id        text NOT NULL,
  class_id             text NOT NULL,
  addr0_id             text NOT NULL,
  PRIMARY KEY (document_id, class_view_id, class_id, addr0_id),
  FOREIGN KEY (document_id, class_view_id)
    REFERENCES rhpf_class_view(document_id, class_view_id) ON DELETE CASCADE,
  FOREIGN KEY (document_id, addr0_id)
    REFERENCES rhpf_addr0(document_id, addr0_id) ON DELETE CASCADE
);

CREATE TABLE rhpf_shadow (
  document_id          text NOT NULL REFERENCES rhpf_document(document_id) ON DELETE CASCADE,
  shadow_id            text NOT NULL,
  rank_id              text NOT NULL,
  phase                text NOT NULL,
  truncation           text NOT NULL,
  congruence           text NOT NULL,
  policy_uri           text,
  is_authoritative     boolean NOT NULL DEFAULT false CHECK (is_authoritative = false),
  PRIMARY KEY (document_id, shadow_id),
  FOREIGN KEY (document_id, rank_id)
    REFERENCES rhpf_rank(document_id, rank_id)
);

CREATE TABLE rhpf_shadow_node (
  document_id          text NOT NULL,
  shadow_node_id       text NOT NULL,
  shadow_id            text NOT NULL,
  kind                 text NOT NULL CHECK (kind IN ('semantic', 'packed', 'intermediate')),
  label                text,
  PRIMARY KEY (document_id, shadow_node_id),
  FOREIGN KEY (document_id, shadow_id)
    REFERENCES rhpf_shadow(document_id, shadow_id) ON DELETE CASCADE
);

CREATE TABLE rhpf_shadow_backing (
  document_id          text NOT NULL,
  shadow_node_id       text NOT NULL,
  backing_id           text NOT NULL,
  PRIMARY KEY (document_id, shadow_node_id, backing_id),
  FOREIGN KEY (document_id, shadow_node_id)
    REFERENCES rhpf_shadow_node(document_id, shadow_node_id) ON DELETE CASCADE
);

CREATE TABLE rhpf_shadow_edge (
  document_id          text NOT NULL,
  shadow_id            text NOT NULL,
  edge_ordinal         bigint GENERATED ALWAYS AS IDENTITY,
  src_shadow_node      text NOT NULL,
  dst_shadow_node      text NOT NULL,
  kind                 text NOT NULL CHECK (kind IN ('contains', 'premise', 'projectsTo')),
  ord                  integer,
  PRIMARY KEY (document_id, shadow_id, edge_ordinal),
  FOREIGN KEY (document_id, shadow_id)
    REFERENCES rhpf_shadow(document_id, shadow_id) ON DELETE CASCADE,
  FOREIGN KEY (document_id, src_shadow_node)
    REFERENCES rhpf_shadow_node(document_id, shadow_node_id) ON DELETE CASCADE,
  FOREIGN KEY (document_id, dst_shadow_node)
    REFERENCES rhpf_shadow_node(document_id, shadow_node_id) ON DELETE CASCADE
);

-- ------------------------------------------------------------
-- Derived view: ordered segment chain per addr0
-- ------------------------------------------------------------
CREATE VIEW rhpf_addr0_segment_chain AS
SELECT
  document_id,
  addr0_id,
  segment_id,
  segment_ordinal,
  rank_id,
  patch_id,
  phase
FROM rhpf_segment
ORDER BY document_id, addr0_id, segment_ordinal;

-- ------------------------------------------------------------
-- Derived view: flatten address pairs and route steps in order
-- ------------------------------------------------------------
CREATE VIEW rhpf_addr0_route_flat AS
SELECT
  a.document_id,
  a.addr0_id,
  s.segment_ordinal,
  p.pair_ordinal,
  rs.step_ordinal,
  rs.kind,
  COALESCE(rs.arg_text, rs.arg_int::text) AS arg_value
FROM rhpf_addr0 a
JOIN rhpf_segment s
  ON s.document_id = a.document_id AND s.addr0_id = a.addr0_id
JOIN rhpf_pair p
  ON p.document_id = s.document_id AND p.segment_id = s.segment_id
LEFT JOIN rhpf_route_step rs
  ON rs.document_id = p.document_id AND rs.pair_id = p.pair_id
ORDER BY a.document_id, a.addr0_id, s.segment_ordinal, p.pair_ordinal, rs.step_ordinal;

-- ------------------------------------------------------------
-- Optional PostgreSQL optimization profile
-- ------------------------------------------------------------
-- If you want an accelerator for route prefixes, PostgreSQL's ltree
-- extension can store hierarchical label paths and supports concatenation,
-- ancestor/descendant tests, and indexing. Keep the normalized tables above
-- as the source of truth; treat ltree columns as caches.

-- ------------------------------------------------------------
-- Append-only enforcement for core tables
-- ------------------------------------------------------------
CREATE OR REPLACE FUNCTION rhpf_reject_mutation()
RETURNS trigger
LANGUAGE plpgsql
AS $$
BEGIN
  RAISE EXCEPTION 'PFF core tables are append-only in this profile; % on % is not allowed', TG_OP, TG_TABLE_NAME;
END;
$$;

CREATE TRIGGER rhpf_document_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_document
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_rank_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_rank
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_patch_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_patch
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_boundary_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_boundary
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_port_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_port
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_chart_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_chart
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_addr0_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_addr0
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_segment_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_segment
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_pair_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_pair
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_route_step_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_route_step
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_hop_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_hop
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_addr1_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_addr1
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_addr1_premise_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_addr1_premise
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_addr2_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_addr2
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_class_view_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_class_view
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_class_member_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_class_member
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_shadow_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_shadow
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_shadow_node_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_shadow_node
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_shadow_backing_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_shadow_backing
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();
CREATE TRIGGER rhpf_shadow_edge_no_update_delete BEFORE UPDATE OR DELETE ON rhpf_shadow_edge
FOR EACH ROW EXECUTE FUNCTION rhpf_reject_mutation();

COMMIT;
