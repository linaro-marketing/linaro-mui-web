import {
  MenuItem,
  SubMenuItem,
} from "components/DropdownMenuItem/DropdownMenuItem.types";
export type MegaMenuContentSection = {
  /**
   * The title to be displayed in the dropdown.
   */
  title: string;
  /**
   * The section items to be displayed in the dropdown.
   */
  options: SubMenuItem[];
};
export type MegaMenuContent = {
  /**
   * The sections to be displayed in the mega menu.
   */
  sections: MegaMenuContentSection[];
};
// Generated with util/create-component.js
export interface MegaMenuContentProps {
  content: MegaMenuContent;
}
