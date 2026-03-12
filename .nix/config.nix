{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  attribute = "TypedExtraction";

  no-rocq-yet = true;

  default-bundle = "9.1";

  bundles."9.1" = {
    coqPackages = {
      coq.override.version = "9.1";
      metarocq.override.version = "v1.5.1-9.1";
    };
    rocqPackages = {
      rocq-core.override.version = "9.1";
    };

    push-branches = ["master"];
  };

  ## Cachix caches to use in CI
  cachix.coq = {};
  cachix.coq-community = {};
  cachix.metarocq = {};

  cachix.au-cobra.authToken = "CACHIX_AUTH_TOKEN";
}
