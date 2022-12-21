// Generated with util/create-component.js

export type FooterLink = {
  /**
   * The title to be displayed in the dropdown.
   */
  title: string;
  /**
   * The pathname to be used in the link.
   */
  pathname: string;
};
export type FooterCol = {
  /**
   * Optional sub header
   */
  title?: string;
  /**
   * The links to be displayed in the column.
   */
  links: FooterLink[];
};
export interface FooterProps {
  columns: FooterCol[];
}
